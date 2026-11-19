# 理杏仁数据库管理.py — 财务数据维护中心
# 完全适配：采集脚本-最新数据.py / 采集脚本-财报数据.py 写入的 fs_data
# 运行：streamlit run 理杏仁数据库管理.py
import io
import re
import math
import functools
import uuid
import html as _html_mod
import time
import ast as _ast
from datetime import datetime
from pathlib import Path
import duckdb
import pandas as pd
import streamlit as st

try:
    import akshare as ak  # noqa: F401
    AKSHARE_OK = True
except ImportError:
    AKSHARE_OK = False

# ========== 配置 ==========
BASE_DIR = Path(__file__).resolve().parent
DUCKLAKE_CATALOG = str(BASE_DIR / "lixinger.ducklake")
DUCKLAKE_DATA_PATH = str(BASE_DIR / "lixinger_files")
COMPANY_CSV = BASE_DIR / "company_list.csv"

ALIAS = "lixinger"
TABLE = f"{ALIAS}.main.fs_data"
METRIC_TABLE = f"{ALIAS}.main.metric_dict"
COMPANY_TABLE = f"{ALIAS}.main.company"
DIM_TABLE = f"{ALIAS}.main.dim_constants"

# ⚠️ 采集脚本真正使用的列名是 table_name（不是 report_type）
KEY_COLS = ["stock_code", "report_period", "granularity", "owner_type",
            "table_name", "field_name", "expr_type"]
VALUE_COLS = ["value", "value_raw"]
ALL_COLS = KEY_COLS + VALUE_COLS

# 兜底选项（dim_constants 读失败时使用）
DEFAULT_GRANULARITIES = ["y", "hy", "q", "latest", "record"]
DEFAULT_OWNER_TYPES = ["consolidated"]
DEFAULT_EXPR_TYPES = ["", "t", "t_y2y", "t_c2c", "t_o", "t_r",
                      "c", "c_y2y", "c_c2c", "c_2y", "c_o", "c_r",
                      "ttm", "ttm_y2y", "ttm_c2c", "ttm_o"]

REPORT_TYPE_LABELS = {
    "hm": "热度指标", "pm": "基本指标",
    "bs": "资产负债表", "ps": "利润表", "cfs": "现金流量表",
    "m": "主要指标", "fs_a": "财务附注",
}
GRANULARITY_LABELS = {
    "y": "年", "hy": "半年", "q": "季度", "m": "月", "w": "周",
    "d": "日", "td": "交易日", "cy": "当年", "fs": "上市以来",
    "y1": "1年", "y3": "3年", "y5": "5年", "y10": "10年", "y20": "20年",
    "record": "记录级", "latest": "最新快照",
}
EXPR_TYPE_LABELS = {
    "": "（无）", "t": "累计", "t_y2y": "累计同比", "t_c2c": "累计环比",
    "t_o": "累计原始", "t_r": "累计回溯", "c": "单季", "c_y2y": "单季同比",
    "c_c2c": "单季环比", "c_2y": "单季年比", "c_o": "单季原始",
    "c_r": "单季回溯", "ttm": "TTM", "ttm_y2y": "TTM同比",
    "ttm_c2c": "TTM环比", "ttm_o": "TTM原始",
}
OWNER_TYPE_LABELS = {"consolidated": "合并报表", "parent_company": "母公司"}

MAX_EDIT_ROWS = 10000

_EMPTY_DICT = {}

st.set_page_config(page_title="财务数据维护中心", page_icon="📊", layout="wide")
st.title("📊 财务数据维护中心")
st.caption(f"DuckLake · {TABLE} · 支持查看 / 编辑 / 新增 / 删除 / 采集 / SQL / 自定义财报")


# ========== 通用工具 ==========
def _safe_str(v):
    if v is None:
        return ""
    if isinstance(v, str):
        return v.strip()
    if isinstance(v, float):
        if v != v:                      # NaN
            return ""
        if v.is_integer():
            return str(int(v))
        return str(v)
    if isinstance(v, int) and not isinstance(v, bool):
        return str(v)
    # 兜底（numpy 标量、Decimal、pd.NA 等）
    try:
        if pd.isna(v):
            return ""
    except Exception:
        pass
    return str(v).strip()

# 常见标量快速排除（这些类型一定不是 NA）
_NA_FAST_NON_NA = (int, str, bytes, bool)

def _is_na(v):
    """快速判断 NA：覆盖 None / float NaN / pd.NA / pd.NaT / np 数值标量。
       常见标量走快速路径，避免 pd.isna 在 hot path 上的开销。"""
    if v is None:
        return True
    if isinstance(v, float):          # 含 np.float64（float 子类）
        return v != v
    if isinstance(v, _NA_FAST_NON_NA):  # int/str/bytes/bool 必然非 NA
        return False
    try:
        return bool(pd.isna(v))        # pd.NA / pd.NaT / np.float32 / Decimal …
    except (TypeError, ValueError):    # list/ndarray 等：pd.isna 返回数组 → 视为非 NA
        return False

def _cell_val(cell):
    if isinstance(cell, dict):
        return cell.get("value")
    return cell

def _pivot_set(pivot: dict, key: str, comp: str, p, et: str, cell: dict):
    bucket = pivot.get(key)
    if bucket is None:
        bucket = pivot[key] = {}
    comp_bucket = bucket.get(comp)
    if comp_bucket is None:
        comp_bucket = bucket[comp] = {}
    per_bucket = comp_bucket.get(p)
    if per_bucket is None:
        per_bucket = comp_bucket[p] = {}
    per_bucket[et] = cell

def _label(mapping, key):
    s = _safe_str(key)
    return mapping.get(s, s)

def _to_cn_date(s):
    """ISO UTC 时间串 → 北京时日期（YYYY-MM-DD）。
    兼容纯日期（2020-04-30）和解析失败的情况，保底取前 10 位。"""
    if not s:
        return ""
    s = str(s).strip()
    if not s:
        return ""
    if "T" not in s and " " not in s:
        return s[:10]
    try:
        _dt = datetime.fromisoformat(s.replace("Z", "+00:00"))
        if _dt.tzinfo is not None:
            from datetime import timezone as _tz, timedelta as _td
            _dt = _dt.astimezone(_tz(_td(hours=8)))
        return _dt.strftime("%Y-%m-%d")
    except Exception:
        return s[:10]

@functools.lru_cache(maxsize=8192)
def _split_period(p):
    """202609 -> ('2026','Q3') ; 20261101 -> ('2026-11-01','')"""
    if p is None:
        return "", ""
    try:
        s = str(int(p))
    except (ValueError, TypeError):
        s = str(p).strip()
    if len(s) == 6:
        yr = s[:4]
        mo = s[4:6]
        q = {'03': 'Q1', '06': 'Q2', '09': 'Q3', '12': 'Q4'}.get(mo, mo)
        return yr, q
    if len(s) == 8:
        return f"{s[:4]}-{s[4:6]}-{s[6:8]}", ""
    return s, ""


def _fmt_value(v, vraw=None):
    # 1) value_raw 是非数字文本 → 原样返回
    #    前提：v 本身也转不成数字（避免误伤 "1.5亿" 这种带单位的数值字段）
    if vraw is not None:
        s = str(vraw).strip()
        if s and s.lower() not in ("nan", "none", "null"):
            vraw_is_number = True
            try:
                float(s.replace(",", ""))
            except ValueError:
                vraw_is_number = False
            if not vraw_is_number:
                # v 也转不成数字才原样返回；v 是数字则走下面的数值格式化
                try:
                    float(v)
                    v_is_number = True
                except Exception:
                    v_is_number = False
                if not v_is_number:
                    return s

    # 2) v 为空
    if v is None:
        return ""
    try:
        if pd.isna(v):
            return ""
    except Exception:
        pass

    # 3) 数值格式化
    try:
        fv = float(v)
    except Exception:
        return ""

    if abs(fv) < 0.005:
        return "0"
    if abs(fv) >= 1e8:
        return f"{fv/1e8:,.2f}亿"
    if abs(fv) >= 1e4:
        return f"{fv/1e4:,.2f}万"
    return f"{fv:,.2f}"


# ===== 百分比/比率类指标（原值列走 _fmt_ratio 显示为 %）=====
PCT_FIELDS = {
    # pm
    "pm.ey", "pm.spc", "pm.spa", "pm.to_r", "pm.dyr", "pm.npatoshopc_cagr",
    "pm.pe_ttm.y10.cvpos", "pm.d_pe_ttm.y10.cvpos",   
    "pm.pb.y10.cvpos", "pm.pb_wo_gw.y10.cvpos",       
    "pm.ps_ttm.y10.cvpos", "pm.dyr.y10.cvpos",        
    # hm
    "hm.tr_dri.p_r", "hm.tr_dri.cagr_p_r_fys",
    "hm.tr_dri.cagr_p_r_fs", "hm.tr_dri.p_r_fs",
    "hm.mm_ha.mm_sh_cap_r",
    "hm.mtasl.mtaslb_mc_r",
    "hm.esc.esc_cap_rc_last", "hm.mssc.mssc_cap_rc_last",
    "hm.elr.srl_cap_r_last", "hm.elr.elr_s_cap_r_y1",
    "hm.ple.ps_sc_r", "hm.ple.ps_shbt10sh_r",
    "hm.npd.tpr_fl", "hm.df.dfr_fs",
    "hm.shnc.shnc_d10", "hm.shnc.shnc_d20", "hm.shnc.shnc_d30", 
    "hm.shnc.shnc_d60", "hm.shnc.shnc_d90",
    "hm.shnc.shnc_q1", "hm.shnc.shnc_q2", "hm.shnc.shnc_q3",
    "hm.shnc.shnc_y1", "hm.shnc.shnc_y2",
    # bs 通用
    "bs.tca_ta_r", "bs.cabb_ta_r", "bs.tnca_ta_r", "bs.ah_ta_r",
    "bs.fa_ta_r", "bs.cip_fa_r", "bs.gw_toe_r", "bs.lwi_ta_r",
    "bs.tl_ta_r", "bs.tcl_tl_r", "bs.tncl_tl_r", "bs.toe_ta_r",
    "bs.shbt1sh_tsc_r", "bs.shbt10sh_tsc_r", "bs.shbt10sh_csc_r",
    "bs.shbt10poof_csc_r", "bs.shbpoof_csc_r", "bs.shbeosh_poof_ecsc_r",
    "bs.dyr",
    # bs 保险/银行/证券特有
    "bs.coresr", "bs.compsr",
    "bs.ct1car", "bs.t1car", "bs.car", "bs.nis", "bs.nim", "bs.lcr",
    "bs.lr_rmb", "bs.lr_fc", "bs.lr_ctrmb",
    "bs.p_pf_mr", "bs.sm_pf_mr", "bs.s_npl_mr", "bs.d_npl_mr",
    "bs.npl_tlaatc_r", "bs.llr_tlaatc_r", "bs.llr_npl_r",
    "bs.tol_tlaatc_r", "bs.lofmt3m_tlaatc_r",
    "bs.rl_tlaatc_r", "bs.rlofmt90d_tlaatc_r",
    "bs.pc_rcr", "bs.pc_clr", "bs.pc_lcr", "bs.pc_nsfr",
    "bs.pc_nc_na_r", "bs.pc_nc_l_r", "bs.pc_na_l_r",
    "bs.pc_pesaid_nc_r", "bs.pc_pnesaid_nc_r",
    # ps
    "ps.gp_m", "ps.crade_r", "ps.se_r", "ps.ae_r", "ps.rade_r",
    "ps.fe_r", "ps.oe_r", "ps.foe_r", "ps.cp_r", "ps.op_s_r",
    "ps.op_op_r", "ps.rade_tp_r", "ps.ite_tp_r", "ps.np_s_r",
    "ps.npadnrpatoshaopc_npatoshopc_r", "ps.wroe", "ps.wdroe",
    "ps.d_gp_m", "ps.d_oi_r", "ps.o_gp_m", "ps.o_oi_r", "ps.d_np_r",
    "ps.spc_a", "ps.tfci_r", "ps.tfsp_r",
    "ps.nii_bi_r", "ps.nonii_bi_r", "ps.c_i_r", "ps.dtuh_tda_r",
    # m
    "m.wroe", "m.wdroe", "m.roe_atoshaopc", "m.roe_adnrpatoshaopc",
    "m.roe_atomsh", "m.roe", "m.roa", "m.rota", "m.roic", "m.roc",
    "m.rorwa", "m.np_s_r", "m.gp_m", "m.tl_ta_r", "m.lwi_ta_r",
    "m.fa_ta_r", "m.crfscapls_oi_r", "m.ncffoa_op_r", "m.ncffoa_np_r",
    "m.crfscapls_ta_r", "m.ncffoa_fa_r", "m.laatc_cd_r",
    "m.cabb_tcl_r", "m.lv_r",
}
# 模式化补齐
for _d in ("7", "14", "30", "60", "90"):
    PCT_FIELDS.add(f"hm.tr_dri.cagr_p_r_d{_d}")
for _y in ("1", "3", "5", "10", "20"):
    PCT_FIELDS.add(f"hm.tr_dri.cagr_p_r_y{_y}")
for _q in ("1", "2", "3", "4"):
    PCT_FIELDS.add(f"hm.mm_ha.mm_sh_cap_rc_q{_q}")
for _d in ("1", "5", "20", "60", "120", "240"):
    PCT_FIELDS.add(f"hm.mtasl.fb_mc_rc_d{_d}")
for _s in ("m1", "m3", "m6", "y1", "y2", "y3"):
    PCT_FIELDS.add(f"hm.esc.esc_cap_rc_{_s}")
    PCT_FIELDS.add(f"hm.mssc.mssc_cap_rc_{_s}")
for _d in ("1", "5", "10", "20", "60", "120", "240"):
    PCT_FIELDS.add(f"hm.tr.tr_d{_d}")
for _d in ("5d", "20d", "60d", "120d", "250d"):
    PCT_FIELDS.add(f"hm.vol.v_{_d}")
    PCT_FIELDS.add(f"hm.vol.td_cr_{_d}")

_FORMULA_REF_RE = re.compile(r'\[\s*formula\.\s*([^\s\[\].]+)\s*\.')
_FORMULA_VALUE_REF_RE = re.compile(
    r'\[\s*[^\s\[\].]+\s*\.\s*[^\s\[\]]+?\s*\]'
)

def _fmt_formula_value(v):
    if _is_na(v):
        return "--"
    try:
        from decimal import Decimal
        d = Decimal(str(v))
        if not d.is_finite():
            return "--"
        if d == 0:
            return "0"
        text = format(d, "f")  # 不使用科学计数法，也不加千位逗号
        return text.rstrip("0").rstrip(".") if "." in text else text
    except Exception:
        return _safe_str(v) or "--"

def _fmt_cell(v, raw, is_pct, header_unit="亿元", custom_unit=None):
    if is_pct:
        txt = _fmt_ratio(v)
        if txt != "--":
            return txt
        s = _safe_str(raw)
        return s if s and s.lower() not in ("", "nan", "none", "null") else "--"

    if custom_unit:
        try: fv = float(v)
        except Exception: return "--"
        if custom_unit == "亿":   return f"{fv/1e8:,.2f}"
        if custom_unit == "百万": return f"{fv/1e6:,.2f}"
        if custom_unit == "万":   return f"{fv/1e4:,.2f}"
        if custom_unit == "壹":   return f"{fv:,.2f}"
        return f"{fv:,.2f}"

    # 空值 / NaN（v != v 对 NaN 为 True，对 None 单独判）
    if _is_na(v):
        s = _safe_str(raw)
        return s if s and s.lower() not in ("", "nan", "none", "null") else "--"

    # raw 是非数字文本 → 原样
    if raw is not None:
        s_raw = _safe_str(raw)
        if s_raw and s_raw.lower() not in ("", "nan", "none", "null"):
            try:
                float(s_raw.replace(",", ""))
            except ValueError:
                return s_raw

    try:
        fv = float(v)
    except Exception:
        return "--"

    if abs(fv) < 0.005:
        return "0"

    # 表头已声明亿元：内联格式化，不做二次函数调用
    if header_unit == "亿元":
        if abs(fv) >= 1e6:
            return f"{fv / 1e8:,.2f}"
        if abs(fv) >= 1e4:
            return f"{fv / 1e4:,.2f}万"
        return f"{fv:,.2f}元"

    # 只有 latest 快照（header_unit="数值"）才走 _fmt_value
    return _fmt_value(v, raw)

def _fmt_ratio(v):
    if v is None:
        return "--"
    if isinstance(v, float) and v != v:
        return "--"
    if not isinstance(v, (int, str, bool)) and not isinstance(v, float):
        try:
            if pd.isna(v):
                return "--"
        except (TypeError, ValueError):
            pass
    try:
        fv = float(v)
    except Exception:
        return "--"
    pct = fv * 100
    if abs(pct) < 1e-9:
        return "0%"
    # 理杏仁：|增长率| >= 1000% 时显示“倍”
    if abs(pct) >= 1000:
        return f"{fv:,.2f}倍"
    # 极小百分比保留 3 位，如 -0.006%
    if abs(pct) < 0.01:
        return f"{pct:.3f}%"
    return f"{pct:.2f}%"   # 正数不加 +

def _hl_class(v, hl_up, hl_down, light_ref=None):
    if v is None:
        return ""
    if isinstance(v, float):
        if v != v:
            return ""
        pct = v * 100
    elif isinstance(v, int) and not isinstance(v, bool):
        pct = v * 100
    else:
        try:
            pct = float(v) * 100
        except Exception:
            return ""
    light = False
    if light_ref is not None:
        try:
            fv = float(light_ref)
            light = abs(fv) < 1e6
        except Exception:
            light = False

    if hl_up and pct >= hl_up:
        return "hl success hl-light" if light else "hl success"
    if hl_down and pct <= hl_down:
        return "hl danger hl-light" if light else "hl danger"
    return ""

# ========== 自定义财报透视：HTML 渲染 ==========
_CUSTOM_TABLE_CSS = """
<style>
.cf-wrap { overflow: auto; max-height: 720px; border: 1px solid #ddd;
           border-radius: 6px; background:#fff; }
.cf-table { font-size: 12px; border-collapse: collapse; width: max-content;
            min-width: 100%;
            font-family: -apple-system, "PingFang SC", "Microsoft YaHei", sans-serif; }
.cf-table thead th {
    background: linear-gradient(to bottom, #fff 0%, #e9e9e9 100%);
    border: 1px solid #ddd; padding: 6px 8px; text-align: center;
    font-weight: 400; white-space: nowrap; color: #333;
    position: sticky; top: 0; z-index: 4;
}
.cf-table thead tr.value-title th {
    font-weight: 400;
    text-align: right;
}
.cf-table thead tr:nth-child(2) th { top: 30px; z-index: 4; }
.cf-table thead tr:nth-child(3) th { top: 60px; z-index: 4;
    background: #f5f5f5; color:#666; }
.cf-table tbody td {
    border-bottom: 1px solid #ddd; padding: 3px 6px; text-align: right;
    white-space: nowrap; color: #333;
    font-variant-numeric: tabular-nums;
    height: 22px;
    vertical-align: middle;
}
.cf-table tbody td.metric-name {
    text-align: left;
    color: #000;
    background: #fff;
    position: sticky; left: 0; z-index: 2;
    font-weight: 500;
    width: 160px; min-width: 160px; max-width: 160px;
    padding-left: 1.2rem;
    white-space: normal;
    word-break: break-word;
    border-right: 1px solid #ddd;
    box-shadow: 2px 0 5px -2px rgba(0,0,0,0.15);
    vertical-align: middle;
    line-height: 1.4;
}
.cf-table tbody td.company-name {
    text-align: center; color: #333; background: #fff;
    position: sticky; left: 160px; z-index: 2;
    width: 90px; min-width: 90px; max-width: 90px;
    font-weight: 500; font-size: 12px;
    border-right: 1px solid #ddd;
    box-shadow: 2px 0 5px -2px rgba(0,0,0,0.15);
    white-space: nowrap;
    overflow: hidden;
    text-overflow: ellipsis;
}
.cf-table tbody td.value-title {
    text-align: center; color: #000; background: #fff;
    position: sticky; left: 250px; z-index: 2;
    min-width: 52px; font-size: 11px;
    border-right: 1px solid #ddd;
}
.cf-table.single-company tbody td.value-title { left: 160px; }
.cf-table tbody td:hover { background: #ddf9ff !important; }
.cf-table tbody tr:hover td { background: transparent; }
.cf-table tbody tr:hover td.metric-name { background: #f0fafc; }
.cf-table tbody tr:hover td.company-name { background: #f0fafc; }
.cf-table tbody tr.last-value td { border-bottom: 1px solid #ccc; } /* 公司之间的分割线 */
.cf-table td.hl .hl { background: rgba(233,233,19,.85) !important; }
.cf-table td.hl .hl.danger { background: red !important; color: #fff; }
.cf-table td.hl .hl.hl-light.success { background: rgba(233,233,19,.2) !important; }
.cf-table td.hl .hl.hl-light.danger  { background: rgba(255,0,0,.2) !important; color: inherit; }
.cf-table th.fixed-col {
    position: sticky; left: 0; z-index: 5; background: #e9e9e9 !important;
    border-right: 2px solid #ccc;
}
.cf-table th.fixed-col .unit { color: #0d6efd; }
.cf-table tr.e-title td.metric-name { color: #099; font-size: 1rem; }
.cf-table tr.e-important td.metric-name { color: #dc3545; }
.cf-table th.spr,
.cf-table td.spr {
    border-right: 1px solid #099;
}
.cf-table td.text-danger { color: #dc3545 !important; }
.cf-table td.text-success { color: #198754 !important; }
.cf-table td.audit-op { text-align: center; }
.cf-table td.value.primary {
    color: #000;
    font-style: normal;
    font-weight: 500;
}
.cf-meta { font-size: 12px; color: #666; margin-bottom: 8px; }
.cf-table tbody td.metric-name.audit-name { color: #055160; font-weight: 500; }
.cf-table td.column-end { border-right: 1px solid #ddd; }
.cf-table td.spr.column-end { border-right: 1px solid #099; }
.cf-table thead th { border-right: 1px solid #ddd; }
.cf-table tbody td { border-right: 1px solid #ddd; }
.cf-table tbody td.metric-name { border-right: none; }
.cf-table tbody td.value > span {
    border: 1px solid transparent;
    border-radius: .2rem;
    display: inline-block;
    padding: .14rem .21rem;
}
.cf-table tbody tr:hover td.value > span { background: #ddf9ff; }
.cf-table tbody td.value-title > span {
    display: inline-block; padding: .14rem .3rem; border-radius: .2rem;
}
.cf-table tbody td.value-title:hover > span { background: #ddf9ff; }
.cf-table tbody td.metric-name .additional-prefix { margin-left: -1rem; }
</style>
"""

def _cell_has_data(cell):
    if cell is None:
        return False
    if isinstance(cell, dict):
        val = cell.get("value"); raw = cell.get("raw")
    else:
        val = cell; raw = None

    # --- 快路径：普通数值/文本 ---
    if val is not None:
        if isinstance(val, float):
            # NaN 或约等于 0 → 落到 raw 检查（与旧版一致）
            if val == val and abs(val) >= 1e-9:
                return True
        elif isinstance(val, (int, bool)):
            if abs(val) >= 1e-9:
                return True
        else:
            try:
                if abs(float(val)) >= 1e-9:
                    return True
            except Exception:
                return True   # 非数字文本（审计意见等）算有效

    # --- 慢路径：val 无效/缺失时看 raw ---
    if raw is not None:
        s = _safe_str(raw).strip().replace(",", "")
        if s and s.lower() not in ("nan", "none", "null", "-", "--"):
            try:
                return abs(float(s)) >= 1e-9
            except ValueError:
                return True
    return False

def _compute_has_data_map(pivot, field_order=None):
    """field_order 传值时只遍历需要的字段（省遍历 formula.X 别名）。"""
    keys = field_order if field_order is not None else pivot.keys()
    result = {}
    for key in keys:
        comp_map = pivot.get(key)
        if not comp_map:
            continue
        et_has = set()
        for comp_data in comp_map.values():
            for pdat in comp_data.values():
                if not pdat: continue
                for et, cell in pdat.items():
                    if et in et_has: continue
                    if _cell_has_data(cell):
                        et_has.add(et)
        if et_has:
            result[key] = et_has
    return result

_VT_LABELS = {
    "t": "累计", "c": "单季", "q2": "单季",
    "q4": "期末值", "q1": "期初值", "avg": "平均值", "ttm": "TTM值",
    "": "最新",
}
def _translate_formula(expr: str, metric_map=None) -> str:
    """把 [table.field.vt] 翻译成 '期末值 营业收入' 这种可读文本。"""
    mm = metric_map if metric_map is not None else METRIC_MAP
    def _repl(m):
        tn = m.group(1).strip()
        fn, vt = _split_field_vt(m.group(2))
        if not fn:
            return m.group(0)
        lbl = _VT_LABELS.get(vt)
        if lbl is None and vt.startswith("y") and vt[1:].isdigit():
            lbl = f"{vt[1:]}年前同期"
        if lbl is None:
            lbl = f"未知({vt})"
        if tn == "formula":
            return f"{lbl}「{fn}」（自定义）"
        return f"{lbl} {mm.get((tn, fn), fn)}"
    return re.sub(r'\[\s*([^\s\[\].]+)\s*\.\s*([^\s\[\]]+?)\s*\]', _repl, expr)

def _render_custom_table(pivot, periods, field_order, show_types,
                         hl_up, hl_down, table_name, companies, company_name="", period_links=None,
                         hide_empty=False, items_meta=None, audit_tips=None, is_latest=False, metric_map=None, cache_key=None, has_data_map=None):
    mm = metric_map if metric_map is not None else METRIC_MAP
    period_links = period_links or {}
    H = _html_mod.escape

    if cache_key is not None:
        cache = st.session_state.get("_cf_html_cache")
        if cache is None:
            cache = st.session_state["_cf_html_cache"] = {}
        if cache_key in cache:
            _html_body, rendered = cache[cache_key]
            # 命中后移到末尾（LRU）
            cache[cache_key] = cache.pop(cache_key)
            st.markdown(_CUSTOM_TABLE_CSS + _html_body, unsafe_allow_html=True)
            return rendered

    st_set = set(show_types or [])
    has_t      = "t" in st_set
    has_c      = "c" in st_set
    has_ttm    = "ttm" in st_set
    has_t_yoy  = "t_y2y" in st_set
    has_t_coc  = "t_c2c" in st_set
    has_c_yoy  = "c_y2y" in st_set
    has_c_2y   = "c_2y" in st_set
    has_c_coc  = "c_c2c" in st_set
    has_ttm_yoy= "ttm_y2y" in st_set
    has_ttm_coc= "ttm_c2c" in st_set
    if not (has_t or has_c or has_ttm):
        has_t = has_c = True

    rows_to_render = []
    if has_t: rows_to_render.append("t")
    if "t_r" in st_set: rows_to_render.append("t_r")
    if has_c: rows_to_render.append("c")
    if "c_r" in st_set: rows_to_render.append("c_r")
    if has_ttm: rows_to_render.append("ttm")

    has_any_yoy = has_t_yoy or has_c_yoy or has_ttm_yoy
    has_any_coc = has_t_coc or has_c_coc or has_ttm_coc
    cols_per_q = 1 + (1 if has_any_yoy else 0) + (1 if has_any_coc else 0) + (1 if has_c_2y else 0)

    def _pv(cell):
        return cell.get("value") if isinstance(cell, dict) else cell

    def _pr(cell):
        return cell.get("raw") if isinstance(cell, dict) else None

    def _pick_yoy(pdat, r):
        if r == "t":
            return pdat.get("t_y2y") if has_t_yoy else None
        if r == "c":
            return pdat.get("c_y2y") if has_c_yoy else None
        if r == "ttm":
            return pdat.get("ttm_y2y") if has_ttm_yoy else None
        return None

    def _pick_coc(pdat, r):
        if r == "t":
            return pdat.get("t_c2c") if has_t_coc else None
        if r == "c":
            return pdat.get("c_c2c") if has_c_coc else None
        if r == "ttm":
            return pdat.get("ttm_c2c") if has_ttm_coc else None
        return None

    thead = "<thead>"
    if is_latest:
        fixed_cols = 3 if len(companies) > 1 else 2
        thead += (f'<tr><th colspan="{fixed_cols}" rowspan="2" class="fixed-col">'
                  f'<span>默认单位: <span class="unit">数值</span></span></th>')
        for p in periods:
            date_str, _ = _split_period(p)
            thead += f'<th colspan="1">{H(date_str)}</th>'
        thead += "</tr>"
        thead += '<tr class="value-title">'
        for _p in periods:
            thead += "<th>原值</th>"
        thead += "</tr></thead>"
    else:
        year_groups = {}
        period_qs = {}
        for p in periods:
            yr, q = _split_period(p)
            year_groups.setdefault(yr, []).append(p)
            period_qs[p] = q

        fixed_cols = 3 if len(companies) > 1 else 2
        thead += (f'<tr><th colspan="{fixed_cols}" rowspan="3" class="fixed-col">'
                  f'<span>默认单位: <span class="unit">亿元</span></span></th>')

        for yr, plist in year_groups.items():
            thead += f'<th colspan="{len(plist)*cols_per_q}" class="spr">{H(yr)}</th>'
        thead += "</tr>"

        thead += "<tr>"
        for yr, plist in year_groups.items():
            for idx, p in enumerate(plist):
                cls = ' class="spr"' if idx == len(plist) - 1 else ""
                info = period_links.get(int(p), "")
                link, announce = "", ""
                if isinstance(info, dict):
                    link = info.get("link", "")
                    raw_date = info.get("date", "")
                    announce = _to_cn_date(raw_date) if raw_date else ""
                elif isinstance(info, str):
                    link = info
                
                icon = ""
                if link:
                    report_name_map = {"Q1": "一季度报告", "Q2": "半年度报告", "Q3": "三季度报告", "Q4": "年度报告"}
                    q = period_qs[p]
                    report_name = report_name_map.get(q, f"{q}报告")
                    ttl = f"{company_name}：{str(p)[:4]}年{report_name}"
                    if announce:
                        ttl += f"(于{announce}公告)"
                    icon = (f'<a href="{H(link)}" target="_blank" title="{ttl}" '
                            f'style="text-decoration:none; margin-left:4px; vertical-align:middle;">'
                            f'<svg xmlns="http://www.w3.org/2000/svg" width="12" height="12" viewBox="0 0 24 24">'
                            f'<path fill="#6c757d" d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"/>'
                            f'<polyline points="14 2 14 8 20 8" fill="none" stroke="#fff" stroke-width="1.5"/>'
                            f'</svg></a>')
                thead += (f'<th colspan="{cols_per_q}"{cls}>'
                          f'{H(period_qs[p])} {icon}</th>')
        thead += "</tr>"

        thead += '<tr class="value-title">'
        for _yr, plist in year_groups.items():
            for idx, _p in enumerate(plist):
                cls = ' class="spr"' if idx == len(plist) - 1 else ""
                val_cls = cls if (not has_any_yoy and not has_any_coc and not has_c_2y) else ""
                thead += f"<th{val_cls}>原值</th>"
                if has_any_yoy:
                    yoy_cls = "" if (has_any_coc or has_c_2y) else cls
                    thead += f"<th{yoy_cls}>同比</th>"
                if has_any_coc:
                    coc_cls = "" if has_c_2y else cls
                    thead += f"<th{coc_cls}>环比</th>"
                if has_c_2y:
                    thead += f"<th{cls}>年比</th>"
        thead += "</tr></thead>"

    last_period_of_group = set()
    if not is_latest:
        for _yr, plist in year_groups.items():
            last_period_of_group.add(plist[-1])

    tbody = ["<tbody>"]
    rendered = 0
    num_comps = len(companies)

    def _get_comp_fdata(fn, comp):
        return pivot.get(fn, _EMPTY_DICT).get(comp, _EMPTY_DICT)

    if has_c_2y: last_col_type = "y2"       # 👈 年比永远是最后一列
    elif has_any_coc: last_col_type = "coc"
    elif has_any_yoy: last_col_type = "yoy"
    else: last_col_type = "val"

    def _td_cls(*parts):
        return " ".join(x.strip() for x in parts if x and x.strip())

    # ==== 构建一次 check_keys ====
    _check_keys = set(rows_to_render)
    if is_latest: _check_keys.add("")
    if has_t_yoy: _check_keys.add("t_y2y")
    if has_t_coc: _check_keys.add("t_c2c")
    if has_c_yoy: _check_keys.update(["c_y2y", "c_2y"])
    if has_c_coc: _check_keys.add("c_c2c")
    if has_ttm: _check_keys.add("ttm")
    if has_ttm_yoy: _check_keys.add("ttm_y2y")
    if has_ttm_coc: _check_keys.add("ttm_c2c")

    _check_keys_set = frozenset(_check_keys)              # ← 新增，供 set 运算
    _PRIORITY_ET = ("t", "c", "ttm",
                    "t_y2y", "c_y2y", "ttm_y2y",
                    "t_c2c", "c_c2c", "ttm_c2c",
                    "c_2y", "t_r", "c_r", "")
    _check_keys = tuple(k for k in _PRIORITY_ET if k in _check_keys_set)
    for fn in field_order:
        if hide_empty:
            if has_data_map is not None:
                et_has = has_data_map.get(fn)
                if not et_has or not (et_has & _check_keys_set):
                    continue
            else:
                # 兜底：外部调用未传 has_data_map 时走旧路径
                has_any = False
                for comp in companies:
                    comp_fdata = pivot.get(fn, _EMPTY_DICT).get(comp)
                    if not comp_fdata:
                        continue
                    for p in periods:
                        pdat = comp_fdata.get(p)
                        if not pdat:
                            continue
                        for et in _check_keys:
                            if _cell_has_data(pdat.get(et)):
                                has_any = True
                                break
                        if has_any: break
                    if has_any: break
                if not has_any:
                    continue

        if items_meta is None: items_meta = {}
        meta = items_meta.get(fn, {})
        if "." in fn:
            real_tab, real_fn = fn.split(".", 1)
        else:
            real_tab, real_fn = table_name, fn
        base_name = mm.get((real_tab, real_fn), "") or real_fn
        is_pct = fn in PCT_FIELDS
        if meta.get("display_type") == "百分比":
            is_pct = True
        custom_unit = meta.get("unit") if meta.get("unit") else None
        add_prefix = meta.get("additional_prefix") or ""
        tr_cls = "e-title" if meta.get("is_title") else ("e-important" if meta.get("is_important") else "")
        name_cn = f"{add_prefix} {base_name}".strip() if add_prefix else base_name
        if add_prefix:
            name_esc = f'<span class="additional-prefix">{H(add_prefix)}</span> {H(base_name)}'
        else:
            name_esc = H(base_name)
        if meta.get("item_type") == "formula":
            _raw_f = _safe_str(meta.get("formula", ""))
            _trans = _translate_formula(_raw_f, mm) if _raw_f else ""
            if _trans and _trans != _raw_f:
                _tip_txt = _trans[:300]
            else:
                _tip_txt = _raw_f[:300]
            _tip = H(_tip_txt)
            # 展示第一家公司、当前页最新一期中，公式每个引用项的取值
            _values_html = ""
            if companies and periods:
                _debug_comp = companies[0]
                _debug_period = periods[0]
                _ref_values = {}

                def _replace_ref(m):
                    ref = m.group(0)
                    if ref not in _ref_values:
                        value = _eval_formula(
                            ref, pivot, _debug_period, _debug_comp,
                            expr_type="t",
                        )
                        _ref_values[ref] = _fmt_formula_value(value)
                    return _ref_values[ref]

                _substituted_formula = _FORMULA_VALUE_REF_RE.sub(
                    _replace_ref, _raw_f
                )
                _values_html = (
                    f'<div><b>代入计算（{H(company_label(_debug_comp))} · '
                    f'{H(str(_debug_period))} · 累计口径）：</b></div>'
                    f'<pre style="white-space:pre-wrap;word-break:break-all;'
                    f'margin:2px 0;font-size:11px;user-select:all">'
                    f'{H(_substituted_formula)}</pre>'
                )
            _details_html = (
                '<details style="margin-top:4px;font-weight:400;font-size:12px">'
                '<summary style="color:#0d6efd;cursor:pointer">展开</summary>'
                '<div style="margin-top:4px;text-align:left">'
                + (f'<div><b>翻译：</b></div>'
                   f'<pre style="white-space:pre-wrap;word-break:break-all;margin:2px 0;'
                   f'font-size:11px;user-select:all">{H(_trans)}</pre>'
                   if (_trans and _trans != _raw_f) else "")
                + _values_html
                + f'<div><b>原始公式：</b></div>'
                  f'<pre style="white-space:pre-wrap;word-break:break-all;margin:2px 0;'
                  f'font-size:11px;user-select:all">{H(_raw_f)}</pre>'
                  f'</div></details>'
            )
            name_esc += f' <small title="{_tip}" style="color:#0d6efd;cursor:help;margin-left:4px">ⓘ</small>'
            name_esc += _details_html
        rendered += 1

        if fn == "fs_a.auditOpinionType":
            if len(companies) == 1:
                tbody.append(f'<tr class="item-1"><td colspan="2" class="metric-name audit-name">审计意见</td>')
                comp = companies[0]
                comp_fdata = _get_comp_fdata(fn, comp)
                for p in periods:
                    pdat = comp_fdata.get(p, {})
                    txt = _pv(pdat.get("t")) or _pv(pdat.get(""))
                    cls = "text-danger" if not txt else "text-success"
                    tip = H(audit_tips.get(comp, {}).get(p, "")) if audit_tips else ""
                    spr_cls = " spr" if (not is_latest and p in last_period_of_group) else ""
                    tbody.append(f'<td colspan="{cols_per_q}" class="{cls}{spr_cls} audit-op" '
                              f'title="{tip}"><span>{H(_safe_str(txt))}</span></td>')
                tbody.append("</tr>")
            else:
                # 多公司：metric-name rowspan=N，每公司一行
                tbody.append(f'<tr class="item-1"><td rowspan="{len(companies)}" class="metric-name audit-name">审计意见</td>')
                for ci, comp in enumerate(companies):
                    if ci > 0:
                        tbody.append('<tr class="item-1">')
                    cname = COMPANY_NAME_MAP.get(_safe_str(comp), comp)
                    tbody.append(f'<td class="company-name">{H(cname)}</td>')
                    tbody.append(f'<td class="value-title"></td>')
                    comp_fdata = _get_comp_fdata(fn, comp)
                    for p in periods:
                        pdat = comp_fdata.get(p, {})
                        txt = _pv(pdat.get("t")) or _pv(pdat.get(""))
                        cls = "text-danger" if not txt else "text-success"
                        tip = H(audit_tips.get(comp, {}).get(p, "")) if audit_tips else ""
                        spr_cls = " spr" if (not is_latest and p in last_period_of_group) else ""
                        tbody.append(f'<td colspan="{cols_per_q}" class="{cls}{spr_cls} audit-op" '
                                  f'title="{tip}"><span>{H(_safe_str(txt))}</span></td>')
                    tbody.append("</tr>")
            continue

        if is_latest:
            tbody.append(f'<tr class="{tr_cls}"><td rowspan="{num_comps}" class="metric-name">{name_esc}</td>')
            for comp_idx, comp in enumerate(companies):
                comp_fdata = _get_comp_fdata(fn, comp)
                cname = COMPANY_NAME_MAP.get(_safe_str(comp), comp)
                if comp_idx > 0: tbody.append(f'<tr class="{tr_cls}">')
                if len(companies) > 1:
                    tbody.append(f'<td class="company-name">{H(cname)}</td>')
                tbody.append(f'<td class="value-title"><span>最新</span></td>')
                for p in periods:
                    pdat = comp_fdata.get(p, {})
                    key_expr = "t" if "t" in pdat else ""
                    k_val = pdat.get(key_expr)
                    tbody.append(f'<td class="value"><span>{_fmt_cell(_pv(k_val), _pr(k_val), is_pct, header_unit="数值")}</span></td>')
                tbody.append("</tr>")
            continue

        rows_per_comp = len(rows_to_render)
        total_rowspan = num_comps * rows_per_comp

        for comp_idx, comp in enumerate(companies):
            comp_fdata = _get_comp_fdata(fn, comp)
            cname = COMPANY_NAME_MAP.get(_safe_str(comp), comp)
            
            for ridx, r in enumerate(rows_to_render):
                label = EXPR_TYPE_LABELS.get(r, r)
                row_classes = ["item-1"]
                if tr_cls: row_classes.insert(0, tr_cls)
                if ridx == len(rows_to_render) - 1: row_classes.append("last-value")
                tr_cls_str = f' class="{" ".join(row_classes)}"'
                
                tbody.append(f'<tr{tr_cls_str}>')
                
                if comp_idx == 0 and ridx == 0:
                    _tip_text = name_cn or (meta.get("formula") or "")
                    _tip = H(str(_tip_text)[:200])
                    tbody.append(
                        f'<td rowspan="{total_rowspan}" class="metric-name" title="{_tip}">'
                        f'{name_esc}</td>')
                
                if len(companies) > 1 and ridx == 0:
                    tbody.append(f'<td rowspan="{rows_per_comp}" class="company-name">{H(cname)}</td>')
                
                tbody.append(f'<td class="value-title"><span>{label}</span></td>')
                
                for p in periods:
                    pdat = comp_fdata.get(p, {})
                    is_last_in_group = p in last_period_of_group
                    spr = " spr" if is_last_in_group else ""
                    
                    v = pdat.get(r)
                    is_last_val = last_col_type == "val"
                    tip_attr = ""
                    light_ref = None if is_pct else (_pv(v) if _pv(v) is not None else _pr(v))
                    if num_comps == 1 and periods and p == periods[0] and not is_latest:
                        tip_attr = f' title="{H(name_cn)} · {H(period_qs[p])}报告（最新）"'
                    
                    tbody.append(f'<td class="{_td_cls("value", "primary", "column-end" if is_last_val else "", spr if is_last_val else "")}"{tip_attr}>'
                              f'<span>{_fmt_cell(_pv(v), _pr(v), is_pct, header_unit="亿元", custom_unit=custom_unit)}</span></td>')
                    
                    if has_any_yoy:
                        yoy = _pick_yoy(pdat, r)
                        yoy_hl = _hl_class(_pv(yoy), hl_up, hl_down, light_ref)
                        is_last_yoy = (last_col_type == "yoy")
                        span_cls = f' class="{yoy_hl}"' if yoy_hl else ''
                        tbody.append(f'<td class="{_td_cls("value", "hl", "column-end" if is_last_yoy else "", spr if is_last_yoy else "")}">'
                                  f'<span{span_cls}>{_fmt_ratio(_pv(yoy))}</span></td>')

                    if has_any_coc:
                        coc = _pick_coc(pdat, r)
                        coc_hl = _hl_class(_pv(coc), hl_up, hl_down, light_ref)
                        is_last_coc = (last_col_type == "coc")
                        span_cls = f' class="{coc_hl}"' if coc_hl else ''
                        tbody.append(f'<td class="{_td_cls("value", "hl", "column-end" if is_last_coc else "", spr if is_last_coc else "")}">'
                                  f'<span{span_cls}>{_fmt_ratio(_pv(coc))}</span></td>')

                    if has_c_2y:
                        y2 = pdat.get("c_2y") if r == "c" else None
                        y2_hl = _hl_class(_pv(y2), hl_up, hl_down, light_ref)
                        is_last_y2 = (last_col_type == "y2")
                        span_cls = f' class="{y2_hl}"' if y2_hl else ''
                        tbody.append(f'<td class="{_td_cls("value", "hl", "column-end" if is_last_y2 else "", spr if is_last_y2 else "")}">'
                                  f'<span{span_cls}>{_fmt_ratio(_pv(y2))}</span></td>')

                tbody.append("</tr>")

    tbody.append("</tbody>")
    table_cls = "cf-table" if len(companies) > 1 else "cf-table single-company"
    _html_body = f'<div class="cf-wrap"><table class="{table_cls}">{thead}{"".join(tbody)}</table></div>'
    st.markdown(_CUSTOM_TABLE_CSS + _html_body, unsafe_allow_html=True)
    st.session_state["_cf_last_html"] = (
        "<html><head><meta charset='utf-8'></head><body>"
        + _CUSTOM_TABLE_CSS + _html_body + "</body></html>"
    )

    if cache_key is not None:
        cache = st.session_state.setdefault("_cf_html_cache", {})
        cache[cache_key] = (_html_body, rendered)
        # 保留最近 4 个 key
        while len(cache) > 4:
            cache.pop(next(iter(cache)))
    return rendered


# ========== 数据库连接 ==========
@st.cache_resource(show_spinner="正在连接 DuckLake…")
def _get_con():
    con = duckdb.connect()
    try:
        con.execute("INSTALL ducklake;")
    except Exception:
        pass
    con.execute("LOAD ducklake;")
    con.execute(
        f"ATTACH 'ducklake:{DUCKLAKE_CATALOG}' AS {ALIAS} "
        f"(DATA_PATH '{DUCKLAKE_DATA_PATH}', OVERRIDE_DATA_PATH true);"
    )
    con.execute(f"USE {ALIAS};")
    try:
        con.execute(f"CALL {ALIAS}.set_option('parquet_compression', 'zstd');")
    except Exception:
        pass
    # ★ 在这里做健康检查（@cache_resource 保证只执行一次）
    con.cursor().execute(f"SELECT 1 FROM {TABLE} LIMIT 0")
    return con


def get_con():
    try:
        return _get_con(), None
    except Exception as e:
        return None, str(e)

con, conn_err = get_con()
if con is None:
    st.error(f"❌ 数据库连接失败：{conn_err}")
    st.caption(
        "常见原因：① DuckLake 文件锁未释放（采集脚本还在跑 / Windows 上延迟）；"
        "② catalog 或 data 目录被占用；③ 路径配置错误。"
    )
    if st.button("🔁 重试连接", type="primary"):
        try:
            if con is not None:
                con.close()
        except Exception:
            pass
        st.cache_resource.clear()
        st.cache_data.clear()
        time.sleep(0.2)      # 给 DuckLake 一点时间释放文件锁（Windows 尤其需要）
        st.rerun()
    st.stop()


def scalar(sql: str, params=None):
    try:
        cur = con.cursor()
        return cur.execute(sql, params or []).fetchone()[0]
    except Exception:
        return None

@st.cache_data(show_spinner=False, ttl=300)
def _dq_table_granularity(_con):
    return _con.cursor().execute(
        f"SELECT table_name, granularity, count(*) AS rows, "
        f"count(DISTINCT stock_code) AS companies FROM {TABLE} "
        f"GROUP BY table_name, granularity ORDER BY rows DESC"
    ).df()

@st.cache_data(show_spinner=False, ttl=300)
def _dq_period_dist(_con):
    return _con.cursor().execute(
        f"SELECT report_period, count(*) AS rows FROM {TABLE} "
        f"WHERE granularity <> 'latest' "
        f"GROUP BY report_period ORDER BY report_period DESC LIMIT 20"
    ).df()

@st.cache_data(show_spinner=False, ttl=300)
def _dq_expr_dist(_con):
    return _con.cursor().execute(
        f"SELECT expr_type, count(*) AS rows FROM {TABLE} "
        f"GROUP BY expr_type ORDER BY rows DESC"
    ).df()

@st.cache_data(show_spinner=False, ttl=300)
def _dq_latest_top(_con):
    return _con.cursor().execute(
        f"SELECT table_name, field_name, count(*) AS rows "
        f"FROM {TABLE} WHERE granularity='latest' "
        f"GROUP BY table_name, field_name ORDER BY rows DESC LIMIT 30"
    ).df()

@st.cache_data(show_spinner=False, ttl=300)
def _dq_all_fields(_con):
    return _con.cursor().execute(
        f"SELECT DISTINCT table_name, field_name FROM {TABLE}"
    ).df()

@functools.lru_cache(maxsize=32)
def _collect_formula_q1_avg_deps_cached(formulas_key):
    need_q1, need_avg = set(), set()
    exprs = {n: e for n, e in formulas_key if n}
    rq1_map, ravg_map, rq4_map = {}, {}, {}
    for name, expr in exprs.items():
        rq1_map[name]  = set(re.findall(r'\[\s*formula\.\s*([^\s\[\].]+)\s*\.q1\s*\]',  expr))
        ravg_map[name] = set(re.findall(r'\[\s*formula\.\s*([^\s\[\].]+)\s*\.avg\s*\]', expr))
        rq4_map[name]  = set(re.findall(r'\[\s*formula\.\s*([^\s\[\].]+)\s*\.q4\s*\]',  expr))
        need_q1.update(rq1_map[name])
        need_avg.update(ravg_map[name])
    changed = True
    while changed:
        changed = False
        for name in list(need_q1):
            new = (rq1_map.get(name, set()) | rq4_map.get(name, set())) - need_q1
            if new: need_q1 |= new; changed = True
        for name in list(need_avg):
            new = (ravg_map.get(name, set()) | rq4_map.get(name, set())) - need_avg
            if new: need_avg |= new; changed = True
    return frozenset(need_q1), frozenset(need_avg)

@st.cache_data(show_spinner=False, ttl=120)
def _cached_total_periods(_con, comp_head, granularity, owner_type,
                          start_period, end_period, report_type):
    month_filter, month_params = "", []
    if report_type != "全部":
        month_map = {"一季报": "03", "中报": "06", "三季报": "09", "年报": "12"}
        month_filter = " AND substr(CAST(report_period AS VARCHAR),5,2) = ? "
        month_params = [month_map[report_type]]
    return _con.cursor().execute(
        f"SELECT count(DISTINCT report_period) FROM {TABLE} "
        f"WHERE stock_code = ? AND granularity = ? AND owner_type = ? "
        f"AND report_period >= ? AND report_period <= ? {month_filter}",
        [comp_head, granularity, owner_type, start_period, end_period]
        + month_params).fetchone()[0]

@st.cache_data(show_spinner=False, ttl=300)
def _period_bounds(_con):
    row = _con.cursor().execute(
        f"SELECT min(report_period), max(report_period) FROM {TABLE} "
        f"WHERE granularity <> 'latest'").fetchone()
    return row if row else (None, None)

@st.cache_data(show_spinner=False, ttl=60)
def _cached_global_formulas(_con):
    try:
        return _con.cursor().execute(
            f"SELECT * FROM {ALIAS}.main.custom_metric_group_item "
            f"WHERE group_id='GLOBAL_FORMULAS'").df()
    except Exception:
        return pd.DataFrame()

@st.cache_data(show_spinner=False, ttl=60)
def scalar_cached(sql: str, params: tuple = ()):
    try:
        return con.cursor().execute(sql, list(params)).fetchone()[0]
    except Exception:
        return None

@st.cache_data(show_spinner=False, ttl=120)
def _cached_companies(_con, table: str):
    return sorted(r[0] for r in _con.cursor().execute(
        f"SELECT DISTINCT stock_code FROM {table} ORDER BY 1").fetchall())

@st.cache_data(show_spinner=False, ttl=120)
def _cached_tables(_con, table: str):
    return sorted(r[0] for r in _con.cursor().execute(
        f"SELECT DISTINCT table_name FROM {table} ORDER BY 1").fetchall())

@st.cache_data(show_spinner=False, ttl=300)
def _cached_metric_dict(_con, metric_table: str):
    return _con.cursor().execute(
        f"SELECT table_name, field_name, name_cn, company_type "
        f"FROM {metric_table} ORDER BY table_name, field_name, "
        f"  CASE WHEN company_type='non_financial' THEN 0 "
        f"       WHEN company_type IS NULL OR company_type='' THEN 1 ELSE 2 END, "
        f"  company_type"
    ).df()

@st.cache_data(show_spinner=False, ttl=300)
def _build_screener_metric_options(_con, metric_table: str):
    """筛选器指标下拉选项 + 元数据（一次性构建，长期缓存）。

    返回：
        opts: tuple[str, ...]           —— 顺序与 _metric_meta 键序一致
        meta: dict[str, tuple(t, f, name_cn, display)]

    失效时机：任何 custom_metric_group_item 写操作后调 .clear()。
    """
    opts, meta = [], {}

    _type_cn_short = {
        "non_financial": "非金融", "bank": "银行", "insurance": "保险",
        "security": "证券", "reit": "REIT", "other_financial": "其他金融",
    }

    # ---- 1. metric_dict ----
    try:
        _md_df = _cached_metric_dict(_con, metric_table)
    except Exception:
        _md_df = pd.DataFrame()

    seen = set()
    if not _md_df.empty:
        # itertuples 比 iterrows 快 5-10x；namedtuple 访问语义安全
        for _r in _md_df.itertuples(index=False):
            _t = _safe_str(_r.table_name)
            _f = _safe_str(_r.field_name)
            if not _t or not _f:
                continue
            _k = f"{_t}.{_f}"
            if _k in seen:
                continue
            seen.add(_k)
            _n = _f if (pd.isna(_r.name_cn) or not _safe_str(_r.name_cn)) else _safe_str(_r.name_cn)
            _ct = _safe_str(_r.company_type)
            _tbl_cn = REPORT_TYPE_LABELS.get(_t, _t)
            if _ct and _ct != "non_financial":
                _type_cn = _type_cn_short.get(_ct, _ct)
                _disp = f"[{_tbl_cn}·{_type_cn}] {_n} ({_f})"
            else:
                _disp = f"[{_tbl_cn}] {_n} ({_f})"
            opts.append(_k)
            meta[_k] = (_t, _f, _n, _disp)

    # ---- 2. 全局公式（原 _fm_df 查询）----
    try:
        _fm_df = _con.cursor().execute(
            f"SELECT display_name FROM {ALIAS}.main.custom_metric_group_item "
            f"WHERE group_id='GLOBAL_FORMULAS' AND item_type='formula' AND display_name IS NOT NULL "
            f"AND display_name <> '' "
            f"ORDER BY display_name"
        ).df()
    except Exception:
        _fm_df = pd.DataFrame()

    seen_f = set()
    if not _fm_df.empty:
        for _r in _fm_df.itertuples(index=False):
            _dn = _safe_str(_r.display_name)
            if not _dn or _dn in seen_f:
                continue
            seen_f.add(_dn)
            _k = f"formula__{_dn}"
            opts.append(_k)
            meta[_k] = ("formula", _dn, _dn, f"[自定义公式] {_dn}")

    return tuple(opts), meta

# ========== 常量池（从 dim_constants 加载） ==========
@st.cache_data(show_spinner=False, ttl=600)
def load_constants(_con) -> dict:
    out = {
        "granularity": list(DEFAULT_GRANULARITIES),
        "owner_type": list(DEFAULT_OWNER_TYPES),
        "expr_type": list(DEFAULT_EXPR_TYPES),
        "audit_opinion": {}  # 🌟 新增：专门用来存审计意见枚举的翻译
    }
    try:
        df = _con.cursor().execute(
            f"SELECT category, code, name_cn, sort_order FROM {DIM_TABLE} "
            f"ORDER BY category, sort_order"
        ).df()
        for cat in ("granularity", "owner_type", "expr_type"):
            vals = df[df["category"] == cat]["code"].astype(str).tolist()
            if vals:
                out[cat] = vals
                
        # 🌟 加载审计意见的翻译映射
        audit_df = df[df["category"] == "audit_opinion"]
        for _, r in audit_df.iterrows():
            out["audit_opinion"][str(r["code"])] = str(r["name_cn"])
    except Exception:
        pass
    if "" not in out["expr_type"]:
        out["expr_type"].insert(0, "")
    return out

CONSTANTS = load_constants(con)
GRANULARITY_OPTIONS = CONSTANTS["granularity"]
OWNER_TYPE_OPTIONS = CONSTANTS["owner_type"]
EXPR_TYPE_OPTIONS = CONSTANTS["expr_type"]
AUDIT_OPINION_LABELS = CONSTANTS.get("audit_opinion", {})  # 🌟 全局使用


# ========== 公司名称映射（优先 DB company 表，fallback CSV） ==========
@st.cache_data(show_spinner=False, ttl=300)
def load_company_names(_con) -> dict:
    result = {}
    try:
        df = _con.cursor().execute(
            f"SELECT stock_code, name, market FROM {COMPANY_TABLE}"
        ).df()
        for _, r in df.iterrows():
            code = _safe_str(r.get("stock_code"))
            name = _safe_str(r.get("name"))
            mkt = _safe_str(r.get("market")).lower()
            if not code or not name:
                continue
            result[code] = name
            if mkt in ("a", "b"):
                result[code.zfill(6)] = name
            elif mkt == "hk":
                result[code.zfill(5)] = name
        if result:
            return result
    except Exception:
        pass
    try:
        if COMPANY_CSV.exists():
            df = pd.read_csv(COMPANY_CSV, encoding="utf-8-sig", dtype=str)
            for _, r in df.iterrows():
                code = str(r.get("stock_code", "")).strip()
                name = str(r.get("name", "")).strip()
                mkt = str(r.get("market", "")).strip().lower()
                if (not code or code.lower() == "nan"
                        or not name or name.lower() == "nan"):
                    continue
                result[code] = name
                if mkt in ("a", "b"):
                    result[code.zfill(6)] = name
                elif mkt == "hk":
                    result[code.zfill(5)] = name
    except Exception:
        pass
    return result


COMPANY_NAME_MAP = load_company_names(con)


def company_label(code: str) -> str:
    name = COMPANY_NAME_MAP.get(_safe_str(code), "")
    return f"{code} - {name}" if name else _safe_str(code)


# ========== 指标中文名映射（从 metric_dict 加载） ==========
@st.cache_data(show_spinner=False, ttl=300)
def load_metric_maps(_con) -> dict:
    maps = {"__all__": {}}
    try:
        df = _con.cursor().execute(
            f"SELECT company_type, table_name, field_name, name_cn FROM {METRIC_TABLE}"
        ).df()
    except Exception:
        return maps
    for ct, t, f, name_cn in df.itertuples(index=False, name=None):
        ct = _safe_str(ct) or "non_financial"
        t = _safe_str(t)
        f = _safe_str(f)
        if not t or not f:
            continue
        name_cn = "" if pd.isna(name_cn) else _safe_str(name_cn)
        maps.setdefault(ct, {})[(t, f)] = name_cn
        maps["__all__"].setdefault((t, f), name_cn)
    return maps

METRIC_MAPS = load_metric_maps(con)
METRIC_MAP = METRIC_MAPS["__all__"]

# ========== 自定义指标组 ==========
def _ensure_custom_tables(cur):
    if st.session_state.get("_custom_tables_ready"):
        return
    cur.execute(f"""
        CREATE TABLE IF NOT EXISTS {ALIAS}.main.custom_metric_group(
          group_id VARCHAR, group_name VARCHAR, table_name VARCHAR,
          granularity VARCHAR, owner_type VARCHAR, sort_order INTEGER,
          company_type VARCHAR)
    """)
    # 旧库补列：单独 try，避免“列已存在”影响后续
    try:
        cur.execute(f"ALTER TABLE {ALIAS}.main.custom_metric_group ADD COLUMN company_type VARCHAR")
    except Exception:
        pass
    cur.execute(f"""
        CREATE TABLE IF NOT EXISTS {ALIAS}.main.custom_metric_group_item(
          group_id VARCHAR, item_order INTEGER, item_type VARCHAR,
          table_name VARCHAR, field_name VARCHAR, formula VARCHAR, 
          display_name VARCHAR, additional_prefix VARCHAR, 
          is_title BOOLEAN, is_important BOOLEAN,
          value_type VARCHAR, display_type VARCHAR, unit VARCHAR, remark VARCHAR)
    """)
    for col, dtype in [("value_type", "VARCHAR"), ("display_type", "VARCHAR"), ("unit", "VARCHAR"), ("remark", "VARCHAR")]:
        try:
            cur.execute(f"ALTER TABLE {ALIAS}.main.custom_metric_group_item ADD COLUMN {col} {dtype}")
        except Exception:
            pass
    st.session_state["_custom_tables_ready"] = True

def _migrate_group_formulas_to_global(cur):
    """旧数据迁移：全局库是公式定义的唯一来源，分组行只保留引用。"""
    cols = (
        "group_id, item_order, item_type, table_name, field_name, formula, "
        "display_name, additional_prefix, is_title, is_important, "
        "value_type, display_type, unit, remark"
    )

    global_rows = cur.execute(
        f"SELECT {cols} FROM {ALIAS}.main.custom_metric_group_item "
        "WHERE group_id='GLOBAL_FORMULAS' AND item_type='formula' "
        "ORDER BY item_order, display_name"
    ).fetchall()

    # 同名全局公式只保留第一条；全局已有定义始终优先于旧分组副本。
    canonical = {}
    for row in global_rows:
        name = _safe_str(row[6])
        formula = _safe_str(row[5])
        if name and formula:
            canonical.setdefault(name, row)

    local_rows = cur.execute(
        f"SELECT {cols} FROM {ALIAS}.main.custom_metric_group_item "
        "WHERE group_id <> 'GLOBAL_FORMULAS' AND item_type='formula' "
        "AND formula IS NOT NULL AND trim(formula) <> '' "
        "ORDER BY group_id, item_order"
    ).fetchall()

    for row in local_rows:
        name = _safe_str(row[6])
        formula = _safe_str(row[5])
        if not formula:
            continue

        # 旧公式没有名字时，为相同正文生成稳定名称。
        if not name:
            name = "legacy_" + uuid.uuid5(
                uuid.NAMESPACE_URL, formula
            ).hex[:12]
            cur.execute(
                f"UPDATE {ALIAS}.main.custom_metric_group_item "
                "SET display_name=? WHERE group_id=? AND item_order=? "
                "AND item_type='formula'",
                [name, row[0], row[1]],
            )

        if name not in canonical:
            canonical[name] = (
                "GLOBAL_FORMULAS", 0, "formula", None, None, formula, name,
                row[7], row[8], row[9], None, row[11], row[12], row[13],
            )

    # 重建全局公式行，消除同名的全局重复项。
    cur.execute(
        f"DELETE FROM {ALIAS}.main.custom_metric_group_item "
        "WHERE group_id='GLOBAL_FORMULAS' AND item_type='formula'"
    )
    for order, row in enumerate(canonical.values()):
        cur.execute(
            f"INSERT INTO {ALIAS}.main.custom_metric_group_item "
            f"({cols}) VALUES ({','.join(['?'] * 14)})",
            ("GLOBAL_FORMULAS", order, *row[2:]),
        )

    # 分组行变为纯引用：保留 group_id、item_order、item_type、display_name。
    cur.execute(
        f"UPDATE {ALIAS}.main.custom_metric_group_item SET "
        "table_name=NULL, field_name=NULL, formula=NULL, "
        "additional_prefix=NULL, is_title=NULL, is_important=NULL, "
        "value_type=NULL, display_type=NULL, unit=NULL, remark=NULL "
        "WHERE group_id <> 'GLOBAL_FORMULAS' AND item_type='formula'"
    )

def _load_groups(cur, table_name=None, granularity=None,
                 owner_type="consolidated", company_type=None):
    _ensure_custom_tables(cur)
    if not st.session_state.get("_formula_refs_migrated"):
        _migrate_group_formulas_to_global(cur)
        _formula_refs_migrated = True
        st.session_state["_formula_refs_migrated"] = True
        _cached_group_items.clear()
        _cached_global_formulas.clear()
        _cached_formula_defs.clear()
    try:
        if company_type:
            df = cur.execute(
                f"SELECT group_id, group_name FROM {ALIAS}.main.custom_metric_group "
                "WHERE owner_type=? "
                "AND (company_type=? OR company_type IS NULL OR company_type='') "
                "ORDER BY sort_order",
                [owner_type, company_type]).df()
        else:
            df = cur.execute(
                f"SELECT group_id, group_name FROM {ALIAS}.main.custom_metric_group "
                "WHERE owner_type=? ORDER BY sort_order",
                [owner_type]).df()
        return df.to_dict("records")
    except Exception:
        return []

DEFAULT_GROUPS = [
    ("资产负债表", ["bs"], ["cabb","sr","pwbaofi","tfa","cdfa","nr","ar","rf","ats","pr","rir","crorir","or","ir","dr","fahursa","i","i_dr","ca","ahfs","ncadwioy","oca","tca","d_blank","claatc","cri","ocri","ltar","ltei","oeii","oncfa","rei","fa","cip","pba","oaga","roua","ia","ia_dr","rade","rade_dr","gw","ltpe","dita","onca","tnca","ta","d_blank","stl","bfcb","pfbaofi","tfl","dfl","np","ap","afc","cl","fasurpa","dfcab","stoa","ssoa","sawp","tp","oap","intp","dp","facp","rip","lhfs","ncldwioy","ocl","tcl","d_blank","icr","ltl","bp","psibp","pcsibp","ll","ltap","ltpoe","cal","ltdi","ditl","oncl","tncl","tl","d_blank","sc","oei","psioei","pcsioei","capr","is","oci","rr","surr","pogr","rtp","tetshaoehopc","etmsh","toe","d_blank"]),
    ("利润表",      ["ps"], ["toi","oi","ii","ep","faci","toc","oc","ie","face","s","ce","iiicr","phdrfpip","rie","tas","se","ae","rade","fe","ieife","iiife","oic","ivi","iifaajv","iftdofamaac","ei","nehb","ciofv","cilor","ailor","adi","op","noi","noe","tp","ite","np","d_blank","npfco","npfdco","d_blank","npatoshopc","npatmsh","natooci","tciatshaoehopc","d_blank","d_blank","d_blank","d_blank","d_blank","d_blank","d_blank","d_blank","d_blank","d_blank","d_blank","d_blank","d_blank","tci","tciatoshopc","tciatmsh","d_blank","beps","deps"]),
    ("现金流量表",   ["cfs"], ["d_blank","crfscapls","niicdadfbaofi","niibfcb","niipfofi","crfp","ncrfrib","niiphd","crfifac","niipfbaofi","niifasurpaioa","ncrfstoa","crfwbot","crrtooa","stciffoa","cpfpcarls","niilaatc","niibwcbbaofi","cpfc","niipwbaofi","cpfifac","cpfphd","cptofe","cpft","cprtooa","stcoffoa","ncffoa","d_blank","crfrci","crfii","crfdofiaolta","ncrfdossaou","crrtoia","stcifia","cpfpfiaolta","cpfi","niipl","ncpfbssaou","cprtoia","stcoffia","ncffia","d_blank","crfai","crfamshibss","crfl","crrtofa","stcifffa","cpfbrp","cpfdapdoi","cpfdapomshpbss","cprtofa","stcofffa","ncfffa","iocacedtfier","niicace","bocaceatpb","bocaceatpe"]),
    ("折旧与摊销",   ["cfs"], ["d_blank","daaorei","dofx_dooaga_dopba","d_blank","aoroua","aoia","aoltde"]),
    ("季报财务分析", [], []),
    ("年报财务分析", [], []),
    ("默认",        [], []),
]
def _ensure_default_group(cur, table_name=None, granularity=None, owner_type="consolidated", company_type="non_financial"):
    existing = _load_groups(cur, owner_type=owner_type, company_type=company_type)
    if existing:
        return existing

    for name, tabs, fields in DEFAULT_GROUPS:
        gid = f"grp_{owner_type}_{uuid.uuid4().hex[:8]}"
        # 这里的 table_name 随便存个空或者标记位即可，因为查询时不认它了
        cur.execute(
            f"INSERT INTO {ALIAS}.main.custom_metric_group "
            "(group_id, group_name, table_name, granularity, owner_type, sort_order, company_type) "
            "VALUES (?,?,?,?,?,0,?)",
            [gid, name, "all", "any", owner_type, company_type])
        actual_tab = tabs[0] if tabs else "bs"
        _rows = []
        for i, fn in enumerate(fields or []):
            if "." in fn:
                tn, fn2 = fn.split(".", 1)
            else:
                tn, fn2 = actual_tab, fn
            _rows.append([gid, i, "field", tn, fn2, None, None, None,
                         False, False, "期末值", "数字", "", ""])
        if _rows:
            _ph = "(" + ",".join(["?"] * 14) + ")"
            _sql = (f"INSERT INTO {ALIAS}.main.custom_metric_group_item "
                    f"(group_id, item_order, item_type, table_name, field_name, formula, "
                    f" display_name, additional_prefix, is_title, is_important, "
                    f" value_type, display_type, unit, remark) VALUES "
                    + ",".join([_ph] * len(_rows)))
            cur.execute(_sql, [x for row in _rows for x in row])
    
    return _load_groups(cur, owner_type=owner_type, company_type=company_type)

@st.cache_data(show_spinner=False, ttl=300)
def _cached_group_items(_con, group_id):
    try:
        cur = _con.cursor()
        items = cur.execute(
            f"SELECT * FROM {ALIAS}.main.custom_metric_group_item "
            "WHERE group_id=? ORDER BY item_order",
            [group_id],
        ).df().to_dict("records")

        global_rows = cur.execute(
            f"SELECT * FROM {ALIAS}.main.custom_metric_group_item "
            "WHERE group_id='GLOBAL_FORMULAS' AND item_type='formula'"
        ).df().to_dict("records")
        global_by_name = {
            _safe_str(row.get("display_name")): row
            for row in global_rows
            if _safe_str(row.get("display_name"))
        }

        for item in items:
            if item.get("item_type") != "formula":
                continue
            definition = global_by_name.get(_safe_str(item.get("display_name")))
            if definition:
                # 若还存在旧副本，也始终以全局定义及其元数据为准。
                for key in (
                    "formula", "additional_prefix", "is_title", "is_important",
                    "value_type", "display_type", "unit", "remark",
                ):
                    item[key] = definition.get(key)
        return items
    except Exception:
        return []

def _invalidate_cf_cache():
    """任何写 custom_metric_group_item 的操作后调用。
       作用：让透视表下次渲染时重算 L2 pivot + HTML。"""
    _cached_group_items.clear()
    _cached_formula_defs.clear()
    _cached_global_formulas.clear()
    try:
        _build_screener_metric_options.clear()   # ← 新增
    except Exception:
        pass
    for _k in ("cf_L2_key", "cf_L2", "_cf_html_cache", "cf_html_cache",
               "cf_export_key", "cf_export_bytes"):
        st.session_state.pop(_k, None)

def _invalidate_groups_cache():
    """分组结构变更后调用：让下次渲染重新从 DB 加载 radio 选项。"""
    st.session_state.pop("cf_groups_key", None)
    st.session_state.pop("cf_groups", None)

def _persist_group_order(cur, groups):
    for i, g in enumerate(groups):
        cur.execute(
            f"UPDATE {ALIAS}.main.custom_metric_group "
            f"SET sort_order=? WHERE group_id=?",
            [i, g["group_id"]])

def _save_group_items(cur, group_id, items):
    cur.execute(f"DELETE FROM {ALIAS}.main.custom_metric_group_item WHERE group_id=?", [group_id])
    if not items:
        _cached_group_items.clear()
        return
    cols = ("(group_id, item_order, item_type, table_name, field_name, formula, "
            " display_name, additional_prefix, is_title, is_important, "
            " value_type, display_type, unit, remark)")
    ph = "(" + ",".join(["?"] * 14) + ")"
    BATCH = 500
    for start in range(0, len(items), BATCH):
        chunk = items[start:start + BATCH]
        values_sql = ",".join([ph] * len(chunk))
        params = []
        for i, it in enumerate(chunk, start=start):
            is_formula = it.get("item_type") == "formula"
            params.extend([
                group_id, i, it.get("item_type", "field"),
                None if is_formula else it.get("table_name"),
                None if is_formula else it.get("field_name"),
                None,  # formula 正文只存 GLOBAL_FORMULAS
                it.get("display_name") if is_formula else None,
                None if is_formula else it.get("additional_prefix"),
                None if is_formula else bool(it.get("is_title")),
                None if is_formula else bool(it.get("is_important")),
                None if is_formula else it.get("value_type", "期末值"),
                None if is_formula else it.get("display_type", "数字"),
                None if is_formula else it.get("unit", ""),
                None if is_formula else it.get("remark", ""),
            ])
        cur.execute(
            f"INSERT INTO {ALIAS}.main.custom_metric_group_item {cols} VALUES {values_sql}",
            params)
    _cached_group_items.clear()
    _cached_formula_defs.clear()

def _convert_c_ternary(text):
    """把类 C 三元 (cond ? a : b) 转成 Python (a if cond else b)。
       只处理用圆括号包裹、且内部不再嵌套括号的情况（覆盖 95% 实用写法）。"""
    import re
    prev = None
    while prev != text and "?" in text:
        prev = text

        def _repl(m):
            cond = m.group(1).strip()
            a = m.group(2).strip()
            b = m.group(3).strip()
            return f"({a} if {cond} else {b})"

        # 最内层、非贪婪；避免吞掉引号内的 ?/:（前提是引号内没有 ?/:）
        text = re.sub(r'\(([^()]*?)\?([^()]*?):([^()]*?)\)', _repl, text)
    return text

@functools.lru_cache(maxsize=512)
def _parse_formula(s: str):
    """同一公式字符串只 AST parse 一次。"""
    return _ast.parse(s, mode="eval")

_FUNC_ALIAS_PAIRS = [
    ("SUM", "sum_"), ("AVERAGE", "avg"), ("AVG", "avg"),
    ("MAX", "max_"), ("MIN", "min_"), ("ABS", "abs_"), ("SIGN", "sign_"),
    ("ROUND", "round_"), ("ROUNDUP", "round_up_"), ("ROUNDDOWN", "round_down_"),
    ("CEILING", "ceiling_"), ("FLOOR", "floor_"),
    ("TRUNC", "trunc_"), ("INT", "int_"), ("MOD", "mod_"),
    ("POWER", "power_"), ("SQRT", "sqrt_"), ("EXP", "exp_"),
    ("LN", "ln_"), ("LOG", "log_"), ("LOG10", "log10_"),
    ("IF", "if_"), ("IFS", "ifs_"), ("IFERROR", "iferror_"), ("IFNA", "ifna_"),
    ("AND", "and_"), ("OR", "or_"), ("NOT", "not_"),
    ("CONCAT", "concat_"), ("CONCATENATE", "concat_"),
    ("TEXTJOIN", "textjoin_"), ("TEXT", "text_"), ("VALUE", "value_"),
    ("LEN", "len_"), ("LEFT", "left_"), ("RIGHT", "right_"), ("MID", "mid_"),
    ("SUBSTITUTE", "substitute_"), ("TRIM", "trim_"),
    ("UPPER", "upper_"), ("LOWER", "lower_"), ("REPT", "rept_"),
    ("ISNUMBER", "isnumber_"), ("ISTEXT", "istext_"),
    ("ISBLANK", "isblank_"), ("ISERROR", "iserror_"), ("ISNA", "isna_"),
    ("NA", "na_"), ("N", "n_"), ("PI", "pi_"),
    ("COUNT", "count_"), ("COUNTA", "counta_"),
    ("SUMPRODUCT", "sumproduct_"), ("NUMBERVALUE", "numbervalue_"),
]


@functools.lru_cache(maxsize=2048)
def _preprocess_formula(s: str):
    """把 _eval_formula 的第 1~4 步（纯字符串变换）结果缓存。
       返回 (模板字符串, refs 元组)；refs 元素：
         ('__range__', (table, f1, f2, vtype))
         ('ref',       (table, field, vtype))
    """
    refs = []

    def _range_repl(m):
        i = len(refs)
        refs.append(("__range__", (m.group(1), m.group(2), m.group(3), m.group(4))))
        return f"_R{i}_"

    def _ref_repl(m):
        i = len(refs)
        t = m.group(1).strip()
        f, vt = _split_field_vt(m.group(2))
        if not f:
            return m.group(0)
        refs.append(("ref", (t, f, vt)))
        return f"_R{i}_"

    s = re.sub(
        r'\[\s*([^\s\[\].]+)\s*\.\s*([^\s\[\].]+)\s*:\s*'
        r'([^\s\[\].]+)\s*\.\s*([^\s\[\].]+)\s*\]',
        _range_repl, s,
    )
    s = re.sub(
        r'\[\s*([^\s\[\].]+)\s*\.\s*([^\s\[\]]+?)\s*\]',
        _ref_repl, s,
    )

    s = (s.replace("（", "(").replace("）", ")")
           .replace("，", ",").replace("；", ";")
           .replace("【", "(").replace("】", ")")
           .replace("“", '"').replace("”", '"')
           .replace("‘", "'").replace("’", "'"))
    s = s.replace("&&", " and ").replace("||", " or ")
    _parts = re.split(r'("(?:[^"\\]|\\.)*"|\'(?:[^\'\\]|\\.)*\')', s)
    s = "".join((p.replace("&", " + ") if i % 2 == 0 else p)
                for i, p in enumerate(_parts))

    s = re.sub(r'(\d+(?:\.\d+)?|\))\s*%', r'(\1/100)', s)
    s = s.replace("<>", "!=")
    s = re.sub(r'(?<![<>!=])=(?!=)', "==", s)
    s = s.replace("^", "**").replace("$", "")
    s = _convert_c_ternary(s)

    for k, v in _FUNC_ALIAS_PAIRS:
        if k == "PI":
            s = re.sub(r'\bPI\b\s*\(\s*\)', "pi_()", s, flags=re.IGNORECASE)
        else:
            s = re.sub(rf'\b{k}\b(?=\s*\()', v, s, flags=re.IGNORECASE)
    s = re.sub(r'\bTRUE\b',  "True",  s, flags=re.IGNORECASE)
    s = re.sub(r'\bFALSE\b', "False", s, flags=re.IGNORECASE)

    return s, tuple(refs)

_REF_RANGE_IDX = {}   # id(pivot) -> (pivot_ref, {table: [fields]})

def _get_ref_index(pivot):
    cached = _REF_RANGE_IDX.get(id(pivot))
    if cached is not None and cached[0] is pivot:
        return cached[1]
    idx = {}
    for k in pivot.keys():
        if k.startswith("formula."):   # 公式伪表不参与范围引用
            continue
        if "." in k:
            t_, f_ = k.split(".", 1)
            idx.setdefault(t_, []).append(f_)
    if len(_REF_RANGE_IDX) > 16:        # 防止 id 复用造成内存膨胀
        _REF_RANGE_IDX.clear()
    _REF_RANGE_IDX[id(pivot)] = (pivot, idx)
    return idx

# ============================================================
# 模块级公式求值环境：所有纯函数 + AST 解释器只定义一次
# ============================================================

def _fnum(x):
    if x is None: return 0.0
    if isinstance(x, bool): return 1.0 if x else 0.0
    if isinstance(x, complex): return float("nan")
    try: return float(x)
    except (TypeError, ValueError):
        try: return float(str(x).replace(",", ""))
        except Exception: return 0.0

def _fflat(a):
    out = []
    stack = [a]
    while stack:
        x = stack.pop()
        if isinstance(x, (list, tuple)):
            stack.extend(reversed(x))
        else:
            out.append(x)
    return out

def _fsum(*a):  return sum(_fnum(x) for x in _fflat(a))
def _favg(*a):
    v = [_fnum(x) for x in _fflat(a)]
    return sum(v) / len(v) if v else 0.0
def _fmax(*a):
    v = [_fnum(x) for x in _fflat(a)]; return max(v) if v else 0.0
def _fmin(*a):
    v = [_fnum(x) for x in _fflat(a)]; return min(v) if v else 0.0
def _fabs(x): return abs(_fnum(x))
def _fsign(x):
    v = _fnum(x); return 1 if v > 0 else (-1 if v < 0 else 0)
def _fround(x, n=0):
    try: return round(_fnum(x), int(n))
    except Exception: return _fnum(x)
def _fround_up(x, n=0):
    try:
        f = 10 ** int(n); return math.ceil(_fnum(x) * f) / f
    except Exception: return _fnum(x)
def _fround_down(x, n=0):
    try:
        f = 10 ** int(n); return math.floor(_fnum(x) * f) / f
    except Exception: return _fnum(x)
def _fceiling(x, s=1):
    try: s = _fnum(s) or 1; return math.ceil(_fnum(x) / s) * s
    except Exception: return _fnum(x)
def _ffloor(x, s=1):
    try: s = _fnum(s) or 1; return math.floor(_fnum(x) / s) * s
    except Exception: return _fnum(x)
def _ftrunc(x, n=0):
    try:
        f = 10 ** int(n); return int(_fnum(x) * f) / f
    except Exception: return _fnum(x)
def _fint(x):
    try: return int(_fnum(x))
    except Exception: return 0
def _fmod(a, b):
    try: return _fnum(a) % _fnum(b)
    except Exception: return float("nan")
def _fpower(a, b):
    try:
        res = _fnum(a) ** _fnum(b)
        if isinstance(res, complex): return float("nan")
        return res
    except Exception: return float("nan")
def _fsqrt(x):
    try: return math.sqrt(_fnum(x))
    except Exception: return float("nan")
def _fexp(x):
    try: return math.exp(_fnum(x))
    except Exception: return 0.0
def _fln(x):
    try: return math.log(_fnum(x))
    except Exception: return float("nan")
def _flog(x, base=10):
    try: return math.log(_fnum(x), _fnum(base))
    except Exception: return float("nan")
def _flog10(x):
    try: return math.log10(_fnum(x))
    except Exception: return float("nan")

def _fif(c, a, b=None):       return a if c else b
def _fiferror(v, fb=None):
    try:
        f = float(v)
        return fb if f != f else v
    except Exception: return fb
def _fifna(v, fb=None):
    if v is None: return fb
    try:
        if isinstance(v, float) and v != v: return fb
    except Exception: pass
    return v
def _fifs(*a):
    for i in range(0, len(a) - 1, 2):
        if a[i]: return a[i + 1]
    return None
def _fand(*a): return all(bool(x) for x in _fflat(a))
def _for(*a):  return any(bool(x) for x in _fflat(a))
def _fnot(x):  return not bool(x)

def _fconcat(*a):
    return "".join("" if x is None else str(x) for x in _fflat(a))
def _ftextjoin(sep, _ign, *a):
    return str(sep).join(str(x) for x in _fflat(a) if x is not None and str(x) != "")
def _ftext(v, fmt=""):
    try: fv = float(v)
    except Exception: return "" if v is None else str(v)
    fmt = str(fmt)
    if "%" in fmt: return f"{fv*100:.2f}%"
    if "." in fmt:
        nd = len(fmt.split(".", 1)[1].strip('"'))
        return f"{fv:.{nd}f}"
    if "¥" in fmt or "￥" in fmt: return f"¥{fv:,.2f}"
    if "," in fmt: return f"{fv:,.2f}"
    return f"{fv}"
def _fvalue(v):
    sv = str(v)
    try:
        r = float(sv.replace(",", "").replace("%", ""))
        return r / 100 if "%" in sv else r
    except Exception: return 0.0
def _flen(v):       return len(str(v)) if v is not None else 0
def _fleft(v, n):   return str(v)[:int(n)] if v is not None else ""
def _fright(v, n):  return str(v)[-int(n):] if v is not None else ""
def _fmid(v, st, n):
    if v is None: return ""
    i = int(st) - 1; return str(v)[i:i + int(n)]
def _fsubstitute(v, old, new, n=None):
    if v is None: return ""
    return str(v).replace(str(old), str(new), int(n) if n else -1)
def _ftrim(v):  return str(v).strip() if v is not None else ""
def _fupper(v): return str(v).upper() if v is not None else ""
def _flower(v): return str(v).lower() if v is not None else ""
def _frept(v, n):
    try: return str(v) * int(n)
    except Exception: return ""

def _fisnumber(v):
    if isinstance(v, bool): return False
    try: float(v); return True
    except Exception: return False
def _fistext(v):  return isinstance(v, str)
def _fisblank(v): return v is None or (isinstance(v, str) and v.strip() == "")
def _fiserror(v): return v is None or (isinstance(v, float) and v != v)
def _fisna(v):    return v is None or (isinstance(v, float) and v != v)
def _fna():       return float("nan")
def _fn(v):
    if isinstance(v, bool): return 1 if v else 0
    return _fnum(v)
def _fcount(*a):  return sum(1 for x in _fflat(a) if _fisnumber(x))
def _fcounta(*a): return sum(1 for x in _fflat(a) if not _fisblank(x))
def _fsumproduct(*a):
    arrs = [_fflat(x) for x in a]
    if not arrs: return 0.0
    n = min(len(x) for x in arrs)
    return sum(math.prod(_fnum(arr[i]) for arr in arrs) for i in range(n))
def _fnumbervalue(text, dec_sep=".", grp_sep=","):
    if text is None: return 0.0
    if isinstance(text, bool): return 1.0 if text else 0.0
    if isinstance(text, (int, float)): return float(text)
    s = str(text).strip()
    if not s: return 0.0
    is_pct = s.endswith("%")
    if is_pct: s = s[:-1].strip()
    if grp_sep: s = s.replace(str(grp_sep), "")
    if dec_sep and dec_sep != ".": s = s.replace(str(dec_sep), ".")
    try: v = float(s)
    except ValueError:
        try: v = float(s.replace(",", ""))
        except Exception: return float("nan")
    return v / 100 if is_pct else v
def _fpi():       return math.pi

_BASE_ENV = {
    "sum_": _fsum, "avg": _favg, "max_": _fmax, "min_": _fmin,
    "abs_": _fabs, "sign_": _fsign,
    "round_": _fround, "round_up_": _fround_up, "round_down_": _fround_down,
    "ceiling_": _fceiling, "floor_": _ffloor, "trunc_": _ftrunc, "int_": _fint,
    "mod_": _fmod, "power_": _fpower, "sqrt_": _fsqrt, "exp_": _fexp,
    "ln_": _fln, "log_": _flog, "log10_": _flog10,
    "if_": _fif, "ifs_": _fifs, "iferror_": _fiferror, "ifna_": _fifna,
    "and_": _fand, "or_": _for, "not_": _fnot,
    "concat_": _fconcat, "textjoin_": _ftextjoin, "text_": _ftext, "value_": _fvalue,
    "len_": _flen, "left_": _fleft, "right_": _fright, "mid_": _fmid,
    "substitute_": _fsubstitute, "trim_": _ftrim, "upper_": _fupper,
    "lower_": _flower, "rept_": _frept, "numbervalue_": _fnumbervalue,
    "isnumber_": _fisnumber, "istext_": _fistext, "isblank_": _fisblank,
    "iserror_": _fiserror, "isna_": _fisna, "na_": _fna, "n_": _fn,
    "count_": _fcount, "counta_": _fcounta, "sumproduct_": _fsumproduct, "pi_": _fpi,
}

# ============ 兼容层：逐字复刻 _ast_ev 的运算语义 ============
def _op_add(a, b):
    if isinstance(a, str) or isinstance(b, str):
        sa = "" if a is None else str(a)
        sb = "" if b is None else str(b)
        return sa + sb
    return _fnum(a) + _fnum(b)

def _op_sub(a, b):      return _fnum(a) - _fnum(b)
def _op_mul(a, b):      return _fnum(a) * _fnum(b)

def _op_div(a, b):
    bb = _fnum(b)
    return _fnum(a) / bb if bb != 0 else float("nan")

def _op_mod(a, b):
    bb = _fnum(b)
    return _fnum(a) % bb if bb != 0 else float("nan")

def _op_floordiv(a, b):
    bb = _fnum(b)
    return _fnum(a) // bb if bb != 0 else float("nan")

def _op_pow(a, b):
    res = _fnum(a) ** _fnum(b)
    if isinstance(res, complex):
        return float("nan")
    return res

def _op_neg(a):         return -_fnum(a)
def _op_pos(a):         return  _fnum(a)
def _op_not(a):         return not bool(a)

def _cmp_eq(a, b):
    if isinstance(a, str) or isinstance(b, str):
        return str(a) == str(b)
    return _fnum(a) == _fnum(b)

def _cmp_ne(a, b):
    if isinstance(a, str) or isinstance(b, str):
        return str(a) != str(b)
    return _fnum(a) != _fnum(b)

def _cmp_gt(a, b):  return _fnum(a) >  _fnum(b)
def _cmp_ge(a, b):  return _fnum(a) >= _fnum(b)
def _cmp_lt(a, b):  return _fnum(a) <  _fnum(b)
def _cmp_le(a, b):  return _fnum(a) <= _fnum(b)
def _cmp_in(a, b):  return a in b
def _cmp_notin(a, b): return a not in b

def _bool_and(*args):
    for v in args:
        if not bool(v): return False
    return True

def _bool_or(*args):
    for v in args:
        if bool(v): return True
    return False

_OPER_FN = {
    _ast.Add: "_op_add", _ast.Sub: "_op_sub", _ast.Mult: "_op_mul",
    _ast.Div: "_op_div", _ast.Mod: "_op_mod", _ast.Pow: "_op_pow",
    _ast.FloorDiv: "_op_floordiv",
}
_CMP_FN = {
    _ast.Eq: "_cmp_eq", _ast.NotEq: "_cmp_ne", _ast.Gt: "_cmp_gt",
    _ast.GtE: "_cmp_ge", _ast.Lt: "_cmp_lt", _ast.LtE: "_cmp_le",
    _ast.In: "_cmp_in", _ast.NotIn: "_cmp_notin",
}

class _CompatTransformer(_ast.NodeTransformer):
    """把 BinOp / UnaryOp / Compare / BoolOp 全部改写为函数调用，
       让运算语义跟原版 _ast_ev 完全一致。"""

    def visit_BinOp(self, node):
        self.generic_visit(node)
        name = _OPER_FN.get(type(node.op))
        if name is None:
            return node
        return _ast.Call(
            func=_ast.Name(id=name, ctx=_ast.Load()),
            args=[node.left, node.right], keywords=[])

    def visit_UnaryOp(self, node):
        self.generic_visit(node)
        if isinstance(node.op, _ast.USub):   name = "_op_neg"
        elif isinstance(node.op, _ast.UAdd): name = "_op_pos"
        elif isinstance(node.op, _ast.Not):  name = "_op_not"
        else: return node
        return _ast.Call(
            func=_ast.Name(id=name, ctx=_ast.Load()),
            args=[node.operand], keywords=[])

    def visit_Compare(self, node):
        self.generic_visit(node)
        if len(node.ops) == 0:
            return node
        if len(node.ops) == 1:
            name = _CMP_FN.get(type(node.ops[0]))
            if name is None: return node
            return _ast.Call(func=_ast.Name(id=name, ctx=_ast.Load()),
                             args=[node.left, node.comparators[0]], keywords=[])
        # 链式：a < b < c → _cmp_lt(a,b) and _cmp_lt(b,c)
        parts = []
        left = node.left
        for op, comp in zip(node.ops, node.comparators):
            name = _CMP_FN.get(type(op))
            if name is None:
                return node       # 有未知比较符，放弃变换
            parts.append(_ast.Call(func=_ast.Name(id=name, ctx=_ast.Load()),
                                   args=[left, comp], keywords=[]))
            left = comp
        return _ast.Call(func=_ast.Name(id="_bool_and", ctx=_ast.Load()),
                         args=parts, keywords=[])

    def visit_BoolOp(self, node):
        self.generic_visit(node)
        if isinstance(node.op, _ast.And):   name = "_bool_and"
        elif isinstance(node.op, _ast.Or):  name = "_bool_or"
        else: return node
        return _ast.Call(
            func=_ast.Name(id=name, ctx=_ast.Load()),
            args=list(node.values), keywords=[])

@functools.lru_cache(maxsize=1024)
def _compile_formula(formula_str: str):
    s0 = formula_str.strip()
    if s0.startswith("="):
        s0 = s0[1:].strip()
    s, refs = _preprocess_formula(s0)
    tree = _parse_formula(s)
    tree = _CompatTransformer().visit(tree)          # ← 新增：AST 变换
    _ast.fix_missing_locations(tree)                 # ← 必须调用
    src = _ast.unparse(tree)                         # 统一用 _ast
    code = compile(src, f'<formula:{s0[:40]}>', 'eval')
    return code, refs

_FORMULA_GLOBALS = {
    "__builtins__": {},
    **_BASE_ENV,
    "_op_add": _op_add, "_op_sub": _op_sub, "_op_mul": _op_mul,
    "_op_div": _op_div, "_op_mod": _op_mod, "_op_pow": _op_pow,
    "_op_floordiv": _op_floordiv,
    "_op_neg": _op_neg, "_op_pos": _op_pos, "_op_not": _op_not,
    "_cmp_eq": _cmp_eq, "_cmp_ne": _cmp_ne, "_cmp_gt": _cmp_gt,
    "_cmp_ge": _cmp_ge, "_cmp_lt": _cmp_lt, "_cmp_le": _cmp_le,
    "_cmp_in": _cmp_in, "_cmp_notin": _cmp_notin,
    "_bool_and": _bool_and, "_bool_or": _bool_or,
}
def _run_formula(code, refs, get_cell, get_range):
    """单次公式求值。get_cell(t, f, vt) / get_range(t, f1, f2, vt) 由调用方闭包提供。"""
    if not refs:
        try:
            return eval(code, _FORMULA_GLOBALS, {})
        except Exception:
            return None
    locals_ns = {}
    for i, (tag, payload) in enumerate(refs):
        if tag == "__range__":
            locals_ns[f"_R{i}_"] = get_range(*payload)
        else:
            locals_ns[f"_R{i}_"] = get_cell(*payload)
    try:
        return eval(code, _FORMULA_GLOBALS, locals_ns)
    except Exception:
        return None

_VT_WHITELIST = frozenset({"t", "ttm", "c", "q1", "q2", "q4", "avg", ""})

def _split_field_vt(body: str):
    """把 'field' 或 'field.vt' 拆开，支持 field 含点。
       'oi.t'                    -> ('oi', 't')
       'pe_ttm.y10.cvpos.t'      -> ('pe_ttm.y10.cvpos', 't')
       'pe_ttm.y10.cvpos'        -> ('pe_ttm.y10.cvpos', '')
       'foo.y3'                  -> ('foo', 'y3')
       'tr_dri.cagr_p_r_fys.ttm' -> ('tr_dri.cagr_p_r_fys', 'ttm')"""
    body = body.strip()
    if "." in body:
        head, tail = body.rsplit(".", 1)
        tail = tail.strip()
        if tail in _VT_WHITELIST or (len(tail) >= 2 and tail[0] == "y" and tail[1:].isdigit()):
            return head.strip(), tail
    return body, ""

_KNOWN_VT = frozenset({"q1", "q4", "avg", "ttm", "q2", "c", "t", ""})
def _eval_formula(formula, pivot, period, company, expr_type="t"):
    if formula is None:
        return None
    s0 = str(formula).strip()
    if not s0:
        return None
    if s0.startswith("="):
        s0 = s0[1:].strip()
    try:
        code, refs = _compile_formula(s0)
    except Exception:
        return None

    # ---------- 引用取值（闭包，依赖本函数的 pivot/company/period/expr_type） ----------
    def _get_cell(t, f, vtype):
        if vtype == "q4":
            if expr_type == "ttm" and t in ("bs", "fs_a"):
                vtype = "t"
            else:
                vtype = expr_type if expr_type else "t"

        if vtype and vtype[0] == 'y' and vtype[1:].isdecimal():
            n_years = int(vtype[1:])
            try:
                p_int = int(period)
            except Exception:
                return float("nan")
            if p_int >= 18000101:
                return float("nan")
            target_p = (p_int // 100 - n_years) * 100 + (p_int % 100)
            target_pdat = pivot.get(f"{t}.{f}", {}).get(company, {}).get(target_p)
            if target_pdat is None:
                return float("nan")
            kind = "ttm" if expr_type == "ttm" else ("c" if expr_type == "c" else "t")
            cell = target_pdat.get(kind, target_pdat.get(""))
            return _cell_val(cell) if cell is not None else float("nan")

        if vtype and vtype not in _KNOWN_VT:
            return float("nan")

        if t == "formula":
            pdat = pivot.get(f"{t}.{f}", {}).get(company, {}).get(period)
            if pdat is None:
                return float("nan")
            if vtype == "ttm":
                cell = pdat.get("ttm")
                return _cell_val(cell) if cell is not None else float("nan")
            if vtype in ("q1", "avg"):
                cell = pdat.get(vtype)
                return _cell_val(cell) if cell is not None else float("nan")
            kind = "c" if vtype in ("q2", "c") else "t"
            return _cell_val(pdat.get(kind, pdat.get("")))

        base_key = f"{t}.{f}"
        pdat = pivot.get(base_key, {}).get(company, {}).get(period)

        if vtype == "ttm":
            return _cell_val(pdat.get("ttm")) if pdat else float("nan")

        if vtype in ("q1", "avg"):
            try:
                p_int = int(period)
            except Exception:
                return 0.0
            kind_for_period = "ttm" if expr_type == "ttm" else ("c" if expr_type == "c" else "t")
            if p_int >= 18000101:
                return _cell_val(pdat.get(kind_for_period, pdat.get(""))) if pdat else 0.0
            if t == "bs":
                year = p_int // 100
                q1_period = (year - 1) * 100 + 12
            else:
                q1_period = p_int - 100
            q1_pdat = pivot.get(base_key, {}).get(company, {}).get(q1_period)
            cur_v = (_cell_val(pdat.get(kind_for_period, pdat.get(""))) or 0.0) if pdat else 0.0
            q1_v  = (_cell_val(q1_pdat.get(kind_for_period, q1_pdat.get(""))) or 0.0) if q1_pdat else 0.0
            if vtype == "q1":
                return q1_v if q1_pdat is not None else cur_v
            if vtype == "avg":
                return (cur_v + q1_v) / 2.0 if q1_pdat is not None else cur_v

        kind = "c" if vtype in ("q2", "c") else "t"
        if pdat is None:
            return 0.0
        return _cell_val(pdat.get(kind, pdat.get("")))

    def _ref_range(t, f1, f2, vtype):
        if f1 == f2:
            return _get_cell(t, f1, vtype)
        fields = _get_ref_index(pivot).get(t, [])
        try:
            i1, i2 = fields.index(f1), fields.index(f2)
        except ValueError:
            return 0.0
        lo, hi = sorted([i1, i2])
        return [_get_cell(t, fields[i], vtype) for i in range(lo, hi + 1)]

    return _run_formula(code, refs, _get_cell, _ref_range)

def _collect_formula_q1_avg_deps(formulas):
    formulas_key = tuple(
        (it.get("display_name") or it.get("formula") or "",
         it.get("formula") or "")
        for it in formulas
    )
    return _collect_formula_q1_avg_deps_cached(formulas_key)

def _prev_quarter_period(p: int) -> int:
    """上一个季度的 report_period（YYYYMM）。"""
    y, m = p // 100, p % 100
    if m <= 3:  return (y - 1) * 100 + 12
    if m <= 6:  return y * 100 + 3
    if m <= 9:  return y * 100 + 6
    return y * 100 + 9

def _normalize_pivot_values(pivot):
    """把 pivot 中所有 value 规整为 float | None；非数字文本保留原样。"""
    for _comps in pivot.values():
        for _periods in _comps.values():
            for _ets in _periods.values():
                for _cell in _ets.values():
                    if not isinstance(_cell, dict):
                        continue
                    v = _cell.get("value")
                    if v is None:
                        continue
                    if isinstance(v, float):
                        continue
                    if isinstance(v, int) and not isinstance(v, bool):
                        _cell["value"] = float(v)
                        continue
                    try:
                        if pd.isna(v):
                            _cell["value"] = None
                            continue
                    except Exception:
                        pass
                    if isinstance(v, str):
                        s = v.replace(",", "").strip()
                        try:
                            _cell["value"] = float(s)
                        except ValueError:
                            pass

def _fill_missing_expr_types(pivot, periods, companies, granularity, only_keys=None, _normalize=True, full_derived_periods=None, needed_derived=None):
    """数据库缺少 t_y2y/t_c2c/c_y2y/c_c2c/c_2y/ttm/ttm_y2y/ttm_c2c 时，
    用已有的 t / c 动态补算（只补缺失，不覆盖已有采集值，不写库）。"""
    if granularity in ("latest", None, ""):
        return
    if _normalize: _normalize_pivot_values(pivot)
    periods = sorted({int(p) for p in periods if p})
    full_set = None if full_derived_periods is None \
        else {int(p) for p in full_derived_periods}

    def _is_full(p):
        return full_set is None or p in full_set

    def _need(k):
        return needed_derived is None or k in needed_derived

    def _get(key, comp, p, et):
        cell = pivot.get(key, {}).get(comp, {}).get(p, {}).get(et)
        if cell is None:
            return None
        v = _cell_val(cell)
        # --- 快路径 ---
        if v is None:
            return None
        if isinstance(v, float):                   # 含 np.float64（float 子类）
            return None if v != v else v
        if isinstance(v, int):                     # 含 bool：float(True)=1.0
            return float(v)
        if isinstance(v, str):
            try:
                return float(v.replace(",", ""))
            except ValueError:
                return None
        # --- 慢路径（稀有类型：pd.NA / pd.NaT / np.float32 / np.bool_ / Decimal）---
        try:
            if pd.isna(v):
                return None
        except (TypeError, ValueError):
            pass
        try:
            return float(v)                        # np.bool_ → 1.0/0.0
        except (TypeError, ValueError):
            return None

    def _set(key, comp, p, et, v):
        if v is None:
            return
        bucket = (pivot.setdefault(key, {})
                      .setdefault(comp, {})
                      .setdefault(p, {}))
        old = bucket.get(et)
        if old is not None:
            ov = _cell_val(old)
            if ov is not None:
                try:
                    if not pd.isna(ov):
                        return
                except Exception:
                    return
        bucket[et] = {"value": v, "raw": None}

    def _ratio(a, b):
        if a is None or b is None or abs(b) < 1e-12:
            return None
        return (a - b) / abs(b)

    keys_to_process = list(only_keys) if only_keys is not None else list(pivot.keys())
    for key in keys_to_process:
        if key.startswith("formula.") or key == "fs_a.auditOpinionType":
            continue
        tab = key.split(".", 1)[0]
        if tab == "fs_a":
            continue

        for comp in companies:
            comp_data = pivot.get(key, {}).get(comp)
            if not comp_data:
                continue

            for p in periods:
                if p not in comp_data:      # ← 跳过该公司没有的期
                    continue
                pdat = comp_data.get(p) or _EMPTY_DICT
                is_full = _is_full(p)

                if is_full:
                    # 累计类
                    if _need("t_y2y") and "t_y2y" not in pdat and pdat.get("t") is not None:
                        _set(key, comp, p, "t_y2y",
                             _ratio(_get(key, comp, p, "t"),
                                    _get(key, comp, p - 100, "t")))
                    if _need("t_c2c") and "t_c2c" not in pdat and pdat.get("t") is not None:
                        _set(key, comp, p, "t_c2c",
                             _ratio(_get(key, comp, p, "t"),
                                    _get(key, comp, _prev_quarter_period(p), "t")))

                    # 单季类
                    if _need("c_y2y") and "c_y2y" not in pdat and pdat.get("c") is not None:
                        _set(key, comp, p, "c_y2y",
                             _ratio(_get(key, comp, p, "c"),
                                    _get(key, comp, p - 100, "c")))
                    if _need("c_c2c") and "c_c2c" not in pdat and pdat.get("c") is not None:
                        _set(key, comp, p, "c_c2c",
                             _ratio(_get(key, comp, p, "c"),
                                    _get(key, comp, _prev_quarter_period(p), "c")))
                    if _need("c_2y") and "c_2y" not in pdat and pdat.get("c") is not None:
                        y = p // 100
                        q4_t = _get(key, comp, y * 100 + 12, "t")  # 查找当年Q4的累计值
                        if q4_t is not None and abs(q4_t) > 1e-12:
                            c_val = _get(key, comp, p, "c")
                            if c_val is not None:
                                _set(key, comp, p, "c_2y", c_val / q4_t)

                # TTM 及派生
                if _need("ttm") and "ttm" not in pdat:
                    if tab == "bs":                       # 时点数
                        _set(key, comp, p, "ttm", _get(key, comp, p, "t"))
                    elif p % 100 == 12:                    # Q4 = 全年累计，直接等于 t
                        _set(key, comp, p, "ttm", _get(key, comp, p, "t"))
                    else:
                        t_p = _get(key, comp, p, "t")
                        y = p // 100
                        t_prev_annual = _get(key, comp, (y - 1) * 100 + 12, "t")
                        t_prev_y      = _get(key, comp, p - 100, "t")
                        if None not in (t_p, t_prev_annual, t_prev_y):
                            _set(key, comp, p, "ttm",
                                 t_p + (t_prev_annual - t_prev_y))
                if is_full:
                    if _need("ttm_y2y") and "ttm_y2y" not in pdat:
                        _set(key, comp, p, "ttm_y2y",
                             _ratio(_get(key, comp, p, "ttm"),
                                    _get(key, comp, p - 100, "ttm")))
                    if _need("ttm_c2c") and "ttm_c2c" not in pdat:
                        _set(key, comp, p, "ttm_c2c",
                             _ratio(_get(key, comp, p, "ttm"),
                                    _get(key, comp, _prev_quarter_period(p), "ttm")))

def _apply_formula_items(pivot, items, periods, companies):
    formulas = [it for it in items if it.get("item_type") == "formula" and it.get("formula")]

    ttm_needed = set()
    for it in items:
        if it.get("item_type") == "formula":
            for m in re.finditer(r'\[\s*formula\.\s*([^\s\[\].]+)\s*\.ttm\s*\]',
                                 it.get("formula") or ""):
                ttm_needed.add(m.group(1))
    _referenced_names = set()
    for it in items:
        if it.get("item_type") == "formula":
            for m in _FORMULA_REF_RE.finditer(it.get("formula") or ""):
                _referenced_names.add(m.group(1))

    formulas_need_q1, formulas_need_avg = _collect_formula_q1_avg_deps(formulas)

    _DYN_VT = ("q1", "q4", "avg", "ttm")
    _dynamic_ref_map = {}
    for _it in formulas:
        _f = _it.get("formula") or ""
        _has = False
        for _m in re.finditer(
            r'\[\s*([^\s\[\].]+)\s*\.\s*([^\s\[\].]+)\s*\.\s*([^\s\[\].]+)\s*\]', _f):
            _vt = _m.group(3)
            if _vt in _DYN_VT or (_vt.startswith("y") and _vt[1:].isdigit()):
                _has = True
                break
        _dynamic_ref_map[_it.get("display_name") or _f] = _has

    # ===== 拓扑排序 =====
    _by_name = {}
    for it in formulas:
        _by_name[it.get("display_name") or it.get("formula")] = it

    _deps = {}
    for it in formulas:
        _key = it.get("display_name") or it.get("formula")
        _refs = set()
        for m in _FORMULA_REF_RE.finditer(it.get("formula") or ""):
            _dep = m.group(1)
            if _dep in _by_name:
                _refs.add(_dep)
        _deps[_key] = _refs

    _ordered, _visited, _visiting, _cyclic = [], set(), set(), set()

    def _visit(name):
        if name in _visited:
            return
        if name in _visiting:
            _cyclic.add(name)
            return
        _visiting.add(name)
        for dep in _deps.get(name, ()):
            _visit(dep)
        _visiting.discard(name)
        _visited.add(name)
        if name in _by_name:
            _ordered.append(name)

    for it in formulas:
        _visit(it.get("display_name") or it.get("formula"))

    if _cyclic:
        st.warning(f"⚠️ 检测到循环依赖，将回退到迭代求解（可能较慢）：{'、'.join(sorted(_cyclic))}")

    if not _cyclic:
        # ========== 快路径：无环，拓扑序一次性写完 ==========
        # 与旧版等价：c/ttm 永远写（不需要时 = val_t），q1/avg 按需写
        for key in _ordered:
            it = _by_name[key]
            f = it.get("formula")
            has_dynamic_ref = _dynamic_ref_map.get(key, False)
            need_ttm = has_dynamic_ref or (key in ttm_needed)
            need_q1  = key in formulas_need_q1
            need_avg = key in formulas_need_avg
            _write_formula_key = key in _referenced_names

            for comp in companies:
                for p in periods:
                    val_t   = _eval_formula(f, pivot, p, comp, expr_type="t")
                    val_c   = _eval_formula(f, pivot, p, comp, expr_type="c")   if has_dynamic_ref else val_t
                    val_ttm = _eval_formula(f, pivot, p, comp, expr_type="ttm") if need_ttm      else val_t

                    vals_to_write = [("t", val_t), ("c", val_c), ("ttm", val_ttm)]
                    if need_q1:
                        vals_to_write.append(("q1",  _eval_formula(f, pivot, p, comp, expr_type="q1")))
                    if need_avg:
                        vals_to_write.append(("avg", _eval_formula(f, pivot, p, comp, expr_type="avg")))

                    for et, val in vals_to_write:
                        cell = {"value": val, "raw": val if isinstance(val, str) else None}
                        _target_keys = (key, f"formula.{key}") if _write_formula_key else (key,)
                        for pk in _target_keys:
                            (pivot.setdefault(pk, {})
                                  .setdefault(comp, {})
                                  .setdefault(p, {}))[et] = cell
    else:
        # ========== 慢路径：有环，逐字复刻旧版迭代 ==========
        def _same(a, b):
            if a != a and b != b:      # NaN == NaN
                return True
            return a == b

        for _ in range(len(formulas) + 1):
            progressed = False
            for it in formulas:                       # 严格按 items 原顺序
                f = it.get("formula")
                key = it.get("display_name") or f
                has_dynamic_ref = _dynamic_ref_map.get(key, False)
                need_ttm = has_dynamic_ref or (key in ttm_needed)
                need_q1  = key in formulas_need_q1
                need_avg = key in formulas_need_avg

                for comp in companies:
                    for p in periods:
                        val_t   = _eval_formula(f, pivot, p, comp, expr_type="t")
                        val_c   = _eval_formula(f, pivot, p, comp, expr_type="c")   if has_dynamic_ref else val_t
                        val_ttm = _eval_formula(f, pivot, p, comp, expr_type="ttm") if need_ttm      else val_t

                        vals_to_write = [("t", val_t), ("c", val_c), ("ttm", val_ttm)]
                        if need_q1:
                            vals_to_write.append(("q1",  _eval_formula(f, pivot, p, comp, expr_type="q1")))
                        if need_avg:
                            vals_to_write.append(("avg", _eval_formula(f, pivot, p, comp, expr_type="avg")))

                        for et, val in vals_to_write:
                            cell = {"value": val, "raw": val if isinstance(val, str) else None}
                            for pk in (key, f"formula.{key}"):
                                bucket = (pivot.setdefault(pk, {})
                                               .setdefault(comp, {})
                                               .setdefault(p, {}))
                                old = bucket.get(et)
                                if old is None or not _same(old.get("value"), val):
                                    bucket[et] = cell
                                    progressed = True
            if not progressed:
                break

    # === 引用完整性检查 ===
    _missing = set()
    for it in formulas:
        for m in _FORMULA_REF_RE.finditer(it.get("formula") or ""):
            name = m.group(1)
            if f"formula.{name}" not in pivot:
                _missing.add(name)
    return _missing

def _collect_formula_base_fields_recursive(formula_expr, formula_defs, visited=None):
    r"""返回公式依赖链中所有底层 (table_name, field_name) 集合（排除 formula 伪表）。
       与 _collect_formula_base_tables_recursive 区别：保留具体字段，不只是表名。
       注意：正则 `[^\s\[\].]+` 说明 field_name 里不能含点（数据库里的复杂字段如
       tr_dri.cagr_p_r_fys 无法在公式里引用，只能作为普通字段直接选）。"""
    if visited is None:
        visited = set()
    base_fields = set()
    _, refs = _preprocess_formula(formula_expr)
    for tag, payload in refs:
        if tag != "ref":
            continue
        t, f, vt = payload
        if t == "formula":
            if f in visited or f not in formula_defs:
                continue
            visited.add(f)
            base_fields |= _collect_formula_base_fields_recursive(
                formula_defs[f], formula_defs, visited)
        else:
            base_fields.add((t, f))
    return base_fields

def _collect_formula_base_tables_recursive(formula_expr, formula_defs, visited=None):
    """递归解析公式依赖链的所有底层表（排除 formula 伪表）。
       例：A=[formula.B.q4] / [ps.oi.q4], B=[ps.ni.q4]*2
       → 返回 {"ps"}（B 的 ps.ni 也扫进来）"""
    if visited is None:
        visited = set()
    base_tables = set()
    refs = re.findall(
        r'\[\s*([^\s\[\].]+)\s*\.\s*([^\s\[\].]+)\s*\.\s*([^\s\[\].]+)\s*\]',
        formula_expr
    )
    for t, f, vt in refs:
        if t == "formula":
            if f in visited or f not in formula_defs:
                continue
            visited.add(f)
            base_tables |= _collect_formula_base_tables_recursive(
                formula_defs[f], formula_defs, visited)
        else:
            base_tables.add(t)
    return base_tables


def _collect_formula_max_years_recursive(formula_expr, formula_defs, visited=None):
    """递归计算依赖链的最大回溯年数。
       规则：[formula.B.yM] 表示 A 需要 B 在 p-M 期的值，
             B 自身若又引用 [formula.C.yN]，则需要 p-M-N 期，
             所以 A 依赖链总回溯 = M + N + ...
       直接 .yN 也算进 max_total。"""
    if visited is None:
        visited = set()
    max_total = 0
    for m in re.finditer(r'\.\s*y(\d+)\s*\]', formula_expr):
        max_total = max(max_total, int(m.group(1)))
    # 全后缀匹配：不仅 [formula.X.yN]，也展开 [formula.X.q4/q1/avg/ttm]
    for m in re.finditer(r'\[\s*formula\.\s*([^\s\[\].]+)\s*\.\s*([^\s\[\].]+)\s*\]', formula_expr):
        sub_name, vt = m.group(1), m.group(2)
        if sub_name in visited or sub_name not in formula_defs:
            continue
        visited.add(sub_name)
        n_here = int(vt[1:]) if re.fullmatch(r'y\d+', vt) else 0
        sub_max = _collect_formula_max_years_recursive(
            formula_defs[sub_name], formula_defs, visited)
        max_total = max(max_total, n_here + sub_max)
    return max_total

@st.cache_data(show_spinner=False, ttl=60)
def _cached_formula_defs(_con):
    """返回 {display_name: formula_expr}。60 秒 TTL，公式库变动后 1 分钟内自动生效。"""
    try:
        _fdf = _con.cursor().execute(
            f"SELECT display_name, formula FROM {ALIAS}.main.custom_metric_group_item "
            f"WHERE group_id='GLOBAL_FORMULAS' AND item_type='formula' AND display_name IS NOT NULL"
        ).df()
    except Exception:
        return {}
    result = {}
    for _r in _fdf.itertuples(index=False):
        _dn, _fexpr = _r
        _dn = _safe_str(_dn)
        _fexpr = _safe_str(_fexpr)
        if _dn and _fexpr and _dn not in result:
            result[_dn] = _fexpr
    return result

# ========== 展示列（只读，不写库） ==========
def add_display_cols(df: pd.DataFrame) -> pd.DataFrame:
    if df is None or df.empty:
        return df
    df = df.copy()

    if "stock_code" in df.columns:
        names = df["stock_code"].map(
            lambda c: COMPANY_NAME_MAP.get(_safe_str(c), ""))
        idx = df.columns.get_loc("stock_code") + 1
        df.insert(idx, "stock_name", names)

    if "table_name" in df.columns and "field_name" in df.columns:
        keys = list(zip(df["table_name"].astype(str),
                        df["field_name"].astype(str)))
        df["field_cn"] = [METRIC_MAP.get(k, "") for k in keys]

    if "table_name" in df.columns:
        _k = df["table_name"].map(_safe_str)
        df["table_cn"] = _k.map(REPORT_TYPE_LABELS).fillna(_k)
    if "granularity" in df.columns:
        _k = df["granularity"].map(_safe_str)
        df["granularity_cn"] = _k.map(GRANULARITY_LABELS).fillna(_k)
    if "expr_type" in df.columns:
        _k = df["expr_type"].map(_safe_str)
        df["expr_cn"] = _k.map(EXPR_TYPE_LABELS).fillna(_k)
    return df


def build_column_config(df_columns):
    cfg = {}
    cols = set(df_columns)
    if "stock_code" in cols:
        cfg["stock_code"] = st.column_config.TextColumn(
            "股票代码", required=True, width="small")
    if "stock_name" in cols:
        cfg["stock_name"] = st.column_config.TextColumn(
            "公司名称", disabled=True, width="medium")
    if "report_period" in cols:
        cfg["report_period"] = st.column_config.NumberColumn(
            "报告期(YYYYMM/YYYYMMDD)", required=True, step=1, width="small")
    if "granularity" in cols:
        cfg["granularity"] = st.column_config.SelectboxColumn(
            "粒度", options=GRANULARITY_OPTIONS, required=True, width="small")
    if "granularity_cn" in cols:
        cfg["granularity_cn"] = st.column_config.TextColumn(
            "粒度(中文)", disabled=True, width="small")
    if "owner_type" in cols:
        cfg["owner_type"] = st.column_config.SelectboxColumn(
            "所有权", options=OWNER_TYPE_OPTIONS, required=True, width="small")
    if "table_name" in cols:
        cfg["table_name"] = st.column_config.TextColumn(
            "表名", required=True, width="small")
    if "table_cn" in cols:
        cfg["table_cn"] = st.column_config.TextColumn(
            "报表类型", disabled=True, width="small")
    if "field_name" in cols:
        cfg["field_name"] = st.column_config.TextColumn(
            "字段名", required=True, width="small")
    if "field_cn" in cols:
        cfg["field_cn"] = st.column_config.TextColumn(
            "字段中文名", disabled=True, width="medium")
    if "expr_type" in cols:
        cfg["expr_type"] = st.column_config.SelectboxColumn(
            "表达式", options=EXPR_TYPE_OPTIONS, required=True, width="small")
    if "expr_cn" in cols:
        cfg["expr_cn"] = st.column_config.TextColumn(
            "表达式(中文)", disabled=True, width="small")
    if "value" in cols:
        cfg["value"] = st.column_config.NumberColumn("数值", width="medium")
    if "value_raw" in cols:
        cfg["value_raw"] = st.column_config.TextColumn("原始值", width="medium")
    return cfg


# ========== 通用查询 ==========
def build_where(companies, tables, period_min, period_max,
                item_kw="", raw_kw="",
                granularities=None, owner_types=None, expr_types=None):
    clauses, params = [], []
    if companies:
        clauses.append(f"stock_code IN ({','.join(['?'] * len(companies))})")
        params.extend(companies)
    if tables:
        clauses.append(f"table_name IN ({','.join(['?'] * len(tables))})")
        params.extend(tables)

    if period_min is not None or period_max is not None:
        if period_min is not None and period_max is not None:
            clauses.append(
                "(granularity = 'latest' OR "
                "(report_period >= ? AND report_period <= ?))")
            params.extend([int(period_min), int(period_max)])
        elif period_min is not None:
            clauses.append(
                "(granularity = 'latest' OR report_period >= ?)")
            params.append(int(period_min))
        elif period_max is not None:
            clauses.append(
                "(granularity = 'latest' OR report_period <= ?)")
            params.append(int(period_max))

    if item_kw:
        clauses.append("field_name ILIKE ?")
        params.append(f"%{item_kw}%")
    if raw_kw:
        clauses.append("value_raw ILIKE ?")
        params.append(f"%{raw_kw}%")
    if granularities:
        clauses.append(f"granularity IN ({','.join(['?'] * len(granularities))})")
        params.extend(granularities)
    if owner_types:
        clauses.append(f"owner_type IN ({','.join(['?'] * len(owner_types))})")
        params.extend(owner_types)
    if expr_types:
        clauses.append(f"expr_type IN ({','.join(['?'] * len(expr_types))})")
        params.extend(expr_types)
    return (" WHERE " + " AND ".join(clauses)) if clauses else "", params


def load_df(where, params, limit=1000, offset=0,
            order_by="stock_code, report_period DESC, table_name, field_name, expr_type, granularity"):
    sql = f"SELECT * FROM {TABLE}{where} ORDER BY {order_by} LIMIT ? OFFSET ?"
    cur = con.cursor()
    df = cur.execute(sql, params + [int(limit), int(offset)]).df()
    return add_display_cols(df)

def filter_panel(prefix: str, defaults=None, show_company=True,
                 show_granularity=True, show_owner_type=True,
                 show_expr_type=True):
    defaults = defaults or {}
    cur = con.cursor()

    all_companies = _cached_companies(con, TABLE)
    all_tables = _cached_tables(con, TABLE)

    year_bounds = _period_bounds(con)
    p_min = year_bounds[0] if year_bounds[0] else None
    p_max = year_bounds[1] if year_bounds[1] else None

    c1, c2, c3 = st.columns([2, 2, 2])
    companies = []
    with c1:
        if show_company:
            companies = st.multiselect(
                "公司", all_companies,
                format_func=company_label,
                default=defaults.get("companies", []),
                key=f"{prefix}_companies")
    with c2:
        tables = st.multiselect(
            "表名（报表类型）", all_tables,
            format_func=lambda t: f"{t} - {_label(REPORT_TYPE_LABELS, t)}",
            default=defaults.get("tables", []),
            key=f"{prefix}_tables")
    with c3:
        if p_min and p_max and p_min < p_max:
            y_range = st.slider(
                "报告期范围 (YYYYMM，仅对财报类生效)",
                min_value=int(p_min), max_value=int(p_max),
                value=(int(p_min), int(p_max)),
                key=f"{prefix}_years")
        elif p_min:
            y_range = (int(p_min), int(p_max))
            st.info(f"报告期仅一期：{p_min}")
        else:
            y_range = (None, None)

    c4, c5, c6 = st.columns([2, 2, 2])
    with c4:
        granularities = []
        if show_granularity:
            granularities = st.multiselect(
                "粒度", GRANULARITY_OPTIONS,
                format_func=lambda x: _label(GRANULARITY_LABELS, x),
                default=defaults.get("granularities", []),
                key=f"{prefix}_gran")
    with c5:
        owner_types = []
        if show_owner_type:
            owner_types = st.multiselect(
                "所有权类型", OWNER_TYPE_OPTIONS,
                format_func=lambda x: _label(OWNER_TYPE_LABELS, x),
                default=defaults.get("owner_types", []),
                key=f"{prefix}_owner")
    with c6:
        expr_types = []
        if show_expr_type:
            expr_types = st.multiselect(
                "表达式类型", EXPR_TYPE_OPTIONS,
                format_func=lambda x: _label(EXPR_TYPE_LABELS, x),
                default=defaults.get("expr_types", []),
                key=f"{prefix}_expr")

    c7, c8 = st.columns([3, 3])
    with c7:
        item_kw = st.text_input("字段名/中文名包含", key=f"{prefix}_item")
    with c8:
        raw_kw = st.text_input("原始值包含", key=f"{prefix}_raw")

    return dict(companies=companies, tables=tables,
                period_min=y_range[0], period_max=y_range[1],
                granularities=granularities, owner_types=owner_types,
                expr_types=expr_types,
                item_kw=item_kw, raw_kw=raw_kw)

# ========== 增量保存 ==========
def _row_key_dict(row):
    return tuple(_safe_str(row.get(c)) for c in KEY_COLS)


def _norm_val(v):
    if v is None:
        return None
    try:
        if pd.isna(v):
            return None
    except Exception:
        pass
    return v


def _diff(a, b):
    a = _norm_val(a)
    b = _norm_val(b)
    if a is None and b is None:
        return False
    if a is None or b is None:
        return True
    try:
        return float(a) != float(b)
    except Exception:
        return str(a) != str(b)


def save_edits(con, original: pd.DataFrame, edited: pd.DataFrame):
    orig = original[[c for c in ALL_COLS if c in original.columns]].copy()
    edit = edited[[c for c in ALL_COLS if c in edited.columns]].copy()

    orig_map = {_row_key_dict(r): r for r in orig.to_dict("records")}
    new_map = {}
    for r in edit.to_dict("records"):
        key = _row_key_dict(r)
        if not all(k for i, k in enumerate(key) if KEY_COLS[i] != "expr_type"):
            continue
        new_map[key] = r

    to_delete = set(orig_map) - set(new_map)
    to_insert = set(new_map) - set(orig_map)
    to_update = set(orig_map) & set(new_map)

    changes = []
    for k in to_update:
        old_r, new_r = orig_map[k], new_map[k]
        if _diff(old_r.get("value"), new_r.get("value")) or \
           _diff(old_r.get("value_raw"), new_r.get("value_raw")):
            changes.append(new_r)
    for k in to_insert:
        changes.append(new_map[k])

    def _batch_delete_by_keys(cur, keys, batch=500):
        if not keys:
            return
        cols = ",".join(KEY_COLS)
        ph_row = "(" + ",".join(["?"] * len(KEY_COLS)) + ")"
        for i in range(0, len(keys), batch):
            chunk = keys[i:i+batch]
            values_sql = ",".join([ph_row] * len(chunk))
            params = [v for k in chunk for v in k]
            cur.execute(
                f"DELETE FROM {TABLE} WHERE ({cols}) IN ({values_sql})",
                params,
            )


    def _batch_insert_rows(cur, rows, batch=500):
        if not rows:
            return
        cols = ",".join(ALL_COLS)
        ph_row = "(" + ",".join(["?"] * len(ALL_COLS)) + ")"
        for i in range(0, len(rows), batch):
            chunk = rows[i:i+batch]
            values_sql = ",".join([ph_row] * len(chunk))
            params = []
            for row in chunk:
                for c in ALL_COLS:
                    v = row.get(c)
                    if c == "value":
                        v = _norm_val(v)
                        if v is not None:
                            try:
                                v = float(v)
                            except Exception:
                                v = None
                    elif c == "report_period":
                        if v is not None and not pd.isna(v):
                            try:
                                v = int(v)
                            except Exception:
                                v = None
                        else:
                            v = None
                    else:
                        v = _norm_val(v)
                    params.append(v)
            cur.execute(f"INSERT INTO {TABLE} ({cols}) VALUES {values_sql}", params)

    cur = con.cursor()
    del_keys = list(to_delete) + [_row_key_dict(r) for r in changes]
    _batch_delete_by_keys(cur, del_keys)
    _batch_insert_rows(cur, changes)
    return len(to_delete), len(changes)


# ========== 侧边栏 ==========
with st.sidebar:
    st.header("📈 全局概览")
    try:
        total = scalar_cached(f"SELECT count(*) FROM {TABLE}") or 0
        n_comp = scalar_cached(f"SELECT count(DISTINCT stock_code) FROM {TABLE}") or 0
        n_tab = scalar_cached(f"SELECT count(DISTINCT table_name) FROM {TABLE}") or 0
        last_period = scalar_cached(
            f"SELECT max(report_period) FROM {TABLE} WHERE granularity <> 'latest'")
        st.metric("总记录数", f"{total:,}")
        c1, c2 = st.columns(2)
        c1.metric("公司数", n_comp)
        c2.metric("表数量", n_tab)
        st.caption(f"最新财报期：{last_period or '—'}")
    except Exception as e:
        st.warning(f"统计失败: {e}")

    st.divider()
    st.caption("💾 数据库")
    st.code(
        f"catalog: {DUCKLAKE_CATALOG}\ndata:    {DUCKLAKE_DATA_PATH}",
        language="text")
    st.caption(f"🧠 指标中文映射：{len(METRIC_MAP):,} 条")
    st.caption(f"🏷️ 公司名称映射：{len(COMPANY_NAME_MAP):,} 条")
    if st.button("🔄 清空缓存并重新连接", width='stretch'):
        try:
            if con is not None:
                con.close()
        except Exception:
            pass
        st.cache_resource.clear()
        st.cache_data.clear()
        # 关键：清掉各个 Tab 和 Dialog 的 session_state
        for k in list(st.session_state.keys()):
            st.session_state.pop(k, None)
        st.rerun()


# ========== Tabs ==========
_TAB_LABELS = [
    "🔍 选股筛选器", "🎯 自定义财报透视", "✏️ 编辑与新增", "🗑️ 批量操作",
    "📈 数据质量", "⚡ 数据采集", "🛠️ SQL 控制台", "⚙️ 表结构管理",
]
active_tab = st.segmented_control(
    "页面导航", _TAB_LABELS,
    default=_TAB_LABELS[0], key="_active_tab",
    label_visibility="collapsed",
)

@st.dialog("编辑筛选条件", width="large")
def _edit_condition_dialog(con, idx):
    _conds = st.session_state.scr_conditions
    if idx < 0 or idx >= len(_conds):
        st.error("条件不存在"); return
    c = _conds[idx]
    _t = c["table_name"]
    _f = c["field_name"]

    st.caption(f"指标：`{_t}.{_f}`  ·  {c.get('name_cn', _f)}")

    # 时间模式
    _tm = st.selectbox("时间", ["最新财报", "指定年份", "最新时间"],
                       index=["最新财报", "指定年份", "最新时间"].index(
                           c.get("time_mode", "最新财报")),
                       key="ec_time")
    _year = _q = None
    if _tm == "指定年份":
        _cc1, _cc2 = st.columns(2)
        with _cc1:
            _year = st.number_input("年", min_value=1990, max_value=2100,
                                    value=int(c.get("year") or 2024), step=1, key="ec_year")
        with _cc2:
            _q = st.selectbox("季", [1, 2, 3, 4],
                              index=[1, 2, 3, 4].index(int(c.get("quarter") or 4)),
                              key="ec_q")

    # 子条件（全量选项，不做 table 过滤）
    _opts = list(EXPR_TYPE_OPTIONS) if _t != "formula" else ["t"]
    _cur_et = c.get("expr_type", "t")
    if _cur_et not in _opts:
        _opts = _opts + [_cur_et]
    _et = st.selectbox("子条件", _opts,
                       index=_opts.index(_cur_et),
                       format_func=lambda x: EXPR_TYPE_LABELS.get(x, x),
                       disabled=(_tm == "最新时间"),
                       key="ec_et")

    # 单位 / 阈值
    _ec1, _ec2, _ec3 = st.columns([1, 1, 1])
    with _ec1:
        _u = st.selectbox("单位", ["壹", "万", "亿", "%"],
                          index=["壹", "万", "亿", "%"].index(c.get("unit", "壹")),
                          key="ec_unit")
    with _ec2:
        _min = st.number_input("最小值", value=c.get("min"), format="%g", key="ec_min")
    with _ec3:
        _max = st.number_input("最大值", value=c.get("max"), format="%g", key="ec_max")

    # 隐藏开关
    _hidden = st.checkbox("隐藏（不参与筛选）", value=c.get("hidden", False), key="ec_hidden")

    b1, b2 = st.columns(2)
    with b1:
        if st.button("取消", width='stretch', key="ec_cancel"):
            st.session_state.pop("scr_edit_idx", None)
            st.rerun()
    with b2:
        if st.button("保存", type="primary", width='stretch', key="ec_ok"):
            # 1) 构造"编辑后的影子条件"，不改动原 c
            _shadow = dict(c)
            _shadow.update({
                "time_mode": _tm, "year": _year, "quarter": _q,
                "expr_type": _et, "unit": _u, "min": _min, "max": _max,
                "hidden": _hidden,
            })

            # 2) 和"除自己外"的其他条件比对签名
            _shadow_sig = _cond_signature(_shadow)
            _conflict_idx = next(
                (i for i, other in enumerate(_conds)
                 if i != idx and _cond_signature(other) == _shadow_sig),
                None,
            )

            if _conflict_idx is not None:
                # 3) 冲突：只报错，不 update、不 pop、不 rerun
                _other = _conds[_conflict_idx]
                st.error(
                    f"⚠️ 保存后将与第 {_conflict_idx + 1} 个条件完全相同：\n\n"
                    f"{_other.get('name_cn', _other.get('field_name', ''))} / "
                    f"{EXPR_TYPE_LABELS.get(_other.get('expr_type', ''), _other.get('expr_type', ''))} / "
                    f"单位={_other.get('unit', '壹')} / "
                    f"min={_other.get('min')} / max={_other.get('max')}\n\n"
                    "请调整阈值/单位/时间后再保存，或先删除那条重复条件。"
                )
            else:
                # 4) 无冲突：正常保存
                _conds[idx].update({
                    "time_mode": _tm, "year": _year, "quarter": _q,
                    "expr_type": _et, "unit": _u, "min": _min, "max": _max,
                    "hidden": _hidden,
                })
                st.session_state.pop("scr_edit_idx", None)
                st.rerun()

# ---------- Tab 0: 选股筛选器（仿理杏仁） ----------
if active_tab == _TAB_LABELS[0]:
    st.subheader("🔍 选股筛选器")
    st.caption("仿理杏仁白马股筛选器：选择范围 → 添加筛选条件 → 开始筛选（多个条件为 AND 关系）")

    _scr_cur = con.cursor()

    # ====== 1. 选择范围 ======
    with st.container(border=True):
        st.markdown("##### 📌 选择范围")
        _rc1, _rc2, _rc3 = st.columns([1, 2, 2])
        with _rc1:
            scr_market = st.selectbox("市场", ["AB股市场", "A股市场", "B股市场"], key="scr_market")
        with _rc2:
            try:
                _ind_df = _scr_cur.execute(
                    f"SELECT DISTINCT industry FROM {COMPANY_TABLE} "
                    f"WHERE industry IS NOT NULL AND industry <> '' ORDER BY industry"
                ).df()
                _industries = _ind_df["industry"].astype(str).tolist()
            except Exception:
                _industries = []
            _ind_mode_col, _ind_sel_col = st.columns([1, 3])
            with _ind_mode_col:
                scr_ind_mode = st.radio(
                    "行业模式", ["包含", "排除"], horizontal=False,
                    key="scr_ind_mode", label_visibility="collapsed")
            with _ind_sel_col:
                scr_industries = st.multiselect(
                    "行业（申万三级）", _industries, key="scr_industries")
        with _rc3:
            try:
                _prov_df = _scr_cur.execute(
                    f"SELECT DISTINCT province FROM {COMPANY_TABLE} "
                    f"WHERE province IS NOT NULL AND province <> '' ORDER BY province"
                ).df()
                _provinces = _prov_df["province"].astype(str).tolist()
            except Exception:
                _provinces = []
            _prov_mode_col, _prov_sel_col = st.columns([1, 3])
            with _prov_mode_col:
                scr_prov_mode = st.radio(
                    "省份模式", ["包含", "排除"], horizontal=False,
                    key="scr_prov_mode", label_visibility="collapsed")
            with _prov_sel_col:
                scr_provinces = st.multiselect("省份", _provinces, key="scr_provinces")

        _rx1, _rx2, _rx3, _rx4 = st.columns(4)
        with _rx1: st.checkbox("排除屏蔽名单", value=False, key="scr_excl_bl",
                               disabled=True, help="需 company.is_blacklist 字段")
        with _rx2: st.checkbox("排除退市股", value=False, key="scr_excl_del",
                               disabled=True, help="需 company.is_delisted 字段")
        with _rx3: st.checkbox("排除 ST", value=False, key="scr_excl_st",
                               help="按公司名称前缀识别：ST / *ST / SST / S*ST")
        with _rx4: st.checkbox("只含 ST", value=False, key="scr_only_st",
                               help="按公司名称前缀识别：ST / *ST / SST / S*ST")
        st.caption("⚠️ 4 个 checkbox 待 company 表补字段后启用。"
                   "市场筛选（AB/A/B）已生效。")

        # A 股板块 ↔ 代码前缀
        _A_BOURSE_PREFIXES = {
            "沪市主板":   ("600", "601", "603", "605"),
            "沪市科创板": ("688", "689"),
            "深圳主板":   ("000", "001", "002", "003"),
            "深圳创业板": ("300", "301"),
            "北京": ("430", "83", "87", "88", "92"),
        }
        _extra_c1, _extra_c2 = st.columns(2)
        with _extra_c1:
            scr_bourse = st.multiselect(
                "交易板块",
                list(_A_BOURSE_PREFIXES.keys()),
                key="scr_bourse",
                help="按股票代码前缀过滤（与「市场」选项互不冲突，可叠加）",
            )
        with _extra_c2:
            scr_mutual = st.checkbox("仅互联互通标的", value=False,
                                     key="scr_mutual_only",
                                     help="占位：需 company.mutual_market 字段")

    # ====== 2. 条件设置 ======
    if "scr_conditions" not in st.session_state:
        st.session_state.scr_conditions = []

    def _cond_label(c):
        _n = c["name_cn"]
        if c["time_mode"] == "指定年份":
            return f"{_n}({int(c['year'] or 2024)}Q{int(c['quarter'] or 4)})"
        if c["time_mode"] == "最新时间":
            return f"{_n}(最新)"
        return _n

    def _cond_signature(c):
        return (
            _safe_str(c.get("table_name")),
            _safe_str(c.get("field_name")),
            _safe_str(c.get("expr_type")),
            _safe_str(c.get("time_mode")),
            _safe_str(c.get("year")),
            _safe_str(c.get("quarter")),
            _safe_str(c.get("unit")),
            _safe_str(c.get("min")),
            _safe_str(c.get("max")),
        )

    with st.container(border=True):
        st.markdown("##### 🔧 条件设置")

        # ========== 加载指标（全部表 + 去重 + 自定义公式） ==========
        _metric_opts, _metric_meta = _build_screener_metric_options(con, METRIC_TABLE)
        _avail_et = EXPR_TYPE_OPTIONS

        with st.expander("➕ 添加筛选条件", expanded=not st.session_state.scr_conditions):
            _ac1, _ac2 = st.columns([3, 2])
            with _ac1:
                _add_metric = st.selectbox(
                    "指标", options=_metric_opts,
                    format_func=lambda k: _metric_meta.get(k, (None, None, k, k))[3],
                    key="scr_add_metric")
            with _ac2:
                _add_time_mode = st.selectbox(
                    "时间", ["最新财报", "指定年份", "最新时间"],
                    key="scr_add_time_mode")

            _ac3, _ac4, _ac5, _ac6, _ac7, _ac8 = st.columns([1, 1, 2, 1.2, 1.4, 1.4])
            with _ac3:
                _add_year = None
                if _add_time_mode == "指定年份":
                    _add_year = st.number_input("年", min_value=1990, max_value=2100,
                                                value=2024, step=1, key="scr_add_year")
            with _ac4:
                _add_quarter = None
                if _add_time_mode == "指定年份":
                    _add_quarter = st.selectbox("季", [1, 2, 3, 4], index=3,
                                                key="scr_add_quarter")
            with _ac5:
                _add_expr = st.selectbox(
                    "子条件", _avail_et,
                    format_func=lambda x: EXPR_TYPE_LABELS.get(x, x),
                    key="scr_add_expr",
                    disabled=(_add_time_mode == "最新时间")
                )
            with _ac6:
                _add_unit = st.selectbox("单位", ["壹", "万", "亿", "%"],
                                          key="scr_add_unit")
            with _ac7:
                _add_min = st.number_input("最小值", value=None,
                                            format="%g", key="scr_add_min")
            with _ac8:
                _add_max = st.number_input("最大值", value=None,
                                            format="%g", key="scr_add_max")

            if st.button("➕ 添加到筛选条件", type="primary",
                         key="scr_btn_add", width='content'):
                if _add_metric in _metric_meta:
                    _t, _f, _n, _ = _metric_meta[_add_metric]
                    _new_cond = {
                        "cond_id": uuid.uuid4().hex[:8],
                        "table_name": _t, "field_name": _f, "name_cn": _n,
                        "time_mode": _add_time_mode,
                        "year": _add_year, "quarter": _add_quarter,
                        "expr_type": _add_expr,
                        "unit": _add_unit, "min": _add_min, "max": _add_max,
                    }

                    # ========== 同名条件检测 ==========
                    _new_sig = _cond_signature(_new_cond)
                    _dup = next(
                        (c for c in st.session_state.scr_conditions
                         if _cond_signature(c) == _new_sig),
                        None,
                    )
                    if _dup is not None:
                        st.warning(
                            f"⚠️ 已存在完全相同条件的行："
                            f"{_dup['name_cn']} / "
                            f"{EXPR_TYPE_LABELS.get(_dup['expr_type'], _dup['expr_type'])} / "
                            f"单位={_dup['unit']} / min={_dup['min']} / max={_dup['max']}"
                        )
                    else:
                        st.session_state.scr_conditions.append(_new_cond)
                        st.rerun()

        # 条件列表
        if not st.session_state.scr_conditions:
            st.info("暂无筛选条件。请在上方添加至少一个条件后开始筛选。")
        else:
            st.markdown(
                f"**当前 {len(st.session_state.scr_conditions)} 个条件**（多个条件为 AND 关系）")
            for _i, _cond in enumerate(list(st.session_state.scr_conditions)):
                _cid = _cond.get("cond_id", str(_i))
                _hidden = _cond.get("hidden", False)
                _c1, _c2, _c3, _c4, _c5, _c6, _c7 = st.columns(
                    [4.5, 2, 0.8, 0.7, 0.7, 0.7, 0.7])

                with _c1:
                    _et_label = EXPR_TYPE_LABELS.get(
                        _cond["expr_type"], _cond["expr_type"])
                    _tm_lbl = ("最新" if _cond["time_mode"] == "最新财报"
                               else f"{_cond.get('year')}Q{_cond.get('quarter')}"
                               if _cond["time_mode"] == "指定年份" else "估值")
                    _prefix = "🙈 " if _hidden else ""
                    if _cond["time_mode"] == "指定年份":
                        st.markdown(
                            f"**{_prefix}{_cond_label(_cond)}** "
                            f"`[{_et_label}]`")
                    else:
                        _tm_lbl = "最新财报" if _cond["time_mode"] == "最新财报" else "最新时间"
                        st.markdown(
                            f"**{_prefix}{_cond_label(_cond)}** "
                            f"`[{_et_label}·{_tm_lbl}]`")
                    # 展示给用户复制的标准公式 ID
                    _qid = f"[{_cond['table_name']}.{_cond['field_name']}.{_cond['expr_type'] or 't'}]"
                    st.code(_qid, language="text")

                with _c2:
                    _u = _cond["unit"]
                    _min_s = "—" if _cond["min"] is None else f"{_cond['min']}{_u if _u != '壹' else ''}"
                    _max_s = "—" if _cond["max"] is None else f"{_cond['max']}{_u if _u != '壹' else ''}"
                    st.markdown(f"min `{_min_s}` / max `{_max_s}`")

                with _c3:
                    st.caption(f"单位：{_cond['unit']}")

                with _c4:
                    if st.button("⏫", key=f"scr_up_{_cid}",
                                 disabled=(_i == 0), width='stretch'):
                        _lst = st.session_state.scr_conditions
                        _lst[_i - 1], _lst[_i] = _lst[_i], _lst[_i - 1]
                        st.rerun()

                with _c5:
                    if st.button("⏬", key=f"scr_dn_{_cid}",
                                 disabled=(_i == len(st.session_state.scr_conditions) - 1),
                                 width='stretch'):
                        _lst = st.session_state.scr_conditions
                        _lst[_i], _lst[_i + 1] = _lst[_i + 1], _lst[_i]
                        st.rerun()

                with _c6:
                    with st.popover("⚙️", help="更多操作"):
                        if st.button("⬆️ 置顶", key=f"scr_top_{_cid}",
                                     disabled=(_i == 0), width='stretch'):
                            _lst = st.session_state.scr_conditions
                            _lst.insert(0, _lst.pop(_i))
                            st.rerun()
                        if st.button("⬇️ 置底", key=f"scr_bot_{_cid}",
                                     disabled=(_i == len(st.session_state.scr_conditions) - 1),
                                     width='stretch'):
                            _lst = st.session_state.scr_conditions
                            _lst.append(_lst.pop(_i))
                            st.rerun()
                        _hide_txt = "👁️ 取消屏蔽" if _hidden else "🙈 屏蔽（不参与筛选）"
                        if st.button(_hide_txt, key=f"scr_hide_{_cid}",
                                     width='stretch'):
                            st.session_state.scr_conditions[_i]["hidden"] = not _hidden
                            st.rerun()
                        if st.button("📋 复制", key=f"scr_dup_{_cid}",
                                     width='stretch'):
                            _d = dict(_cond)
                            _d["cond_id"] = uuid.uuid4().hex[:8]
                            st.session_state.scr_conditions.insert(_i + 1, _d)
                            st.rerun()
                        if st.button("✏️ 编辑", key=f"scr_edit_{_cid}",
                                     width='stretch'):
                            st.session_state["scr_edit_idx"] = _i
                            st.rerun()

                with _c7:
                    if st.button("🗑️", key=f"scr_del_{_cid}", width='stretch'):
                        st.session_state.scr_conditions.pop(_i)
                        st.rerun()

    # ====== 2.5 自定义运算指标（公式筛选条件）======
    with st.container(border=True):
        st.markdown("##### 🧮 自定义运算指标（作为筛选条件）")
        st.caption("直接在此定义公式，会自动存入全局公式库。语法见 [🎯 自定义财报透视] 页的公式编辑器。")

        _cur_f = con.cursor()
        try:
            _gf_df = _cur_f.execute(
                f"SELECT display_name, formula FROM {ALIAS}.main.custom_metric_group_item "
                f"WHERE group_id='GLOBAL_FORMULAS' AND item_type='formula' "
                f"AND display_name IS NOT NULL ORDER BY display_name"
            ).df()
        except Exception:
            _gf_df = pd.DataFrame()
        _gf_map = {_safe_str(r["display_name"]): _safe_str(r["formula"])
                   for _, r in _gf_df.iterrows()} if not _gf_df.empty else {}

        # ===== 编辑现有公式（inline 编辑器）=====
        if _gf_map:
            _edit_sel_col, _edit_act_col = st.columns([3, 1])
            with _edit_sel_col:
                _edit_fname = st.selectbox(
                    "✏️ 编辑已有公式",
                    options=[""] + list(_gf_map.keys()),
                    key="scr_edit_formula_pick")
            with _edit_act_col:
                st.write("")
                _del_clicked = st.button("🗑️ 删除", key="scr_del_formula_btn",
                                         width='stretch',
                                         disabled=not _edit_fname)

            if _edit_fname:
                _edit_expr_val = st.text_area(
                    f"编辑「{_edit_fname}」的公式",
                    value=_gf_map[_edit_fname], height=100,
                    key=f"scr_edit_expr_{_edit_fname}")
                _e1, _e2 = st.columns(2)
                with _e1:
                    if st.button("💾 保存修改", key="scr_save_edit_formula",
                                 type="primary", width='stretch'):
                        _cur_f.execute(
                            f"UPDATE {ALIAS}.main.custom_metric_group_item "
                            f"SET formula=? WHERE group_id='GLOBAL_FORMULAS' "
                            f"AND display_name=?",
                            [_edit_expr_val, _edit_fname])
                        st.toast(f"✅ 已更新「{_edit_fname}」", icon="💾")
                        _invalidate_cf_cache()
                        st.rerun()
                with _e2:
                    if st.button("📋 载入到下方新建", key="scr_copy_to_new",
                                 width='stretch'):
                        st.session_state["scr_f_name"] = _edit_fname
                        st.session_state["scr_f_expr"] = _edit_expr_val
                        st.rerun()

            if _del_clicked and _edit_fname:
                _cur_f.execute(
                    f"DELETE FROM {ALIAS}.main.custom_metric_group_item "
                    f"WHERE item_type='formula' AND display_name=?",
                    [_edit_fname])
                _invalidate_cf_cache()
                st.rerun()

            st.divider()

        _fc1, _fc2 = st.columns([1, 3])
        with _fc1:
            _scr_f_name = st.text_input("指标名", key="scr_f_name",
                                        placeholder="例：五年营收CAGR")
        with _fc2:
            _scr_f_expr = st.text_area(
                "公式", height=90, key="scr_f_expr",
                placeholder="例：power([ps.oi.ttm]/[ps.oi.t],1/5)-1")

        # 公式翻译（与财报透视一致：灰底 + 原地替换）
        if _scr_f_expr:
            _VT_LABELS = {
                # 选股语境（_eval_formula 支持的 t/c/yN）
                "t": "当期", "c": "单季", "q2": "单季",
                # 透视语境（与 _metric_settings_dialog 完全一致）
                "q4": "期末值", "q1": "期初值", "avg": "平均值",
                "ttm": "TTM",
                # 无后缀默认累计
                "": "当期",
            }

            def _repl_ref(m):
                _tn = m.group(1).strip()
                _fn, _vt = _split_field_vt(m.group(2))
                if not _fn:
                    return m.group(0)
                    
                _lbl = _VT_LABELS.get(_vt)
                if _lbl is None and _vt.startswith("y") and _vt[1:].isdigit():
                    _lbl = f"{_vt[1:]}年前同期"
                if _lbl is None:
                    _lbl = f"未知({_vt})"     # 显式提示写错后缀
                    
                if _tn == "formula":
                    return f"{_lbl}「{_fn}」（自定义公式）"
                _nm = METRIC_MAP.get((_tn, _fn), _fn)
                return f"{_lbl} {_nm}".strip()

            _desc = re.sub(
                r'\[\s*([^\s\[\].]+)\s*\.\s*([^\s\[\]]+?)\s*\]',
                _repl_ref, _scr_f_expr)
            st.markdown(
                f"<div style='background:#f8f9fa; padding:10px; border-radius:4px; "
                f"font-size:14px;'>详情：{_desc}</div>",
                unsafe_allow_html=True)

        # 从已有公式载入（必须点按钮才覆盖输入框）
        if _gf_map:
            _f_pick = st.selectbox(
                "从已有公式中载入",
                options=[""] + list(_gf_map.keys()),
                key="scr_f_pick")
            if _f_pick:
                def _do_load_formula(_n=_f_pick, _e=_gf_map[_f_pick]):
                    st.session_state["scr_f_name"] = _n
                    st.session_state["scr_f_expr"] = _e
                st.button(f"📋 载入「{_f_pick}」", key="scr_f_load",
                          width='content',
                          on_click=_do_load_formula)

        # 时间 / 单位 / 阈值
        _ft1, _ft2, _ft3, _ft4, _ft5, _ft6 = st.columns([1.2, 0.8, 0.8, 0.8, 1, 1])
        with _ft1:
            _scr_f_time = st.selectbox("时间", ["最新财报", "指定年份"], key="scr_f_time")
        with _ft2:
            _scr_f_year = st.number_input("年", min_value=1990, max_value=2100, value=2024,
                                          step=1, key="scr_f_year",
                                          disabled=(_scr_f_time != "指定年份"))
        with _ft3:
            _scr_f_q = st.selectbox("季", [1, 2, 3, 4], index=3, key="scr_f_q",
                                    disabled=(_scr_f_time != "指定年份"))
        with _ft4:
            _scr_f_unit = st.selectbox("单位", ["壹", "万", "亿", "%"], key="scr_f_unit")
        with _ft5:
            _scr_f_min = st.number_input("最小值", value=None, format="%g", key="scr_f_min")
        with _ft6:
            _scr_f_max = st.number_input("最大值", value=None, format="%g", key="scr_f_max")

        if st.button("➕ 添加为筛选条件", type="primary", key="scr_f_add",
                     disabled=not (_scr_f_name and _scr_f_expr)):
            if any(c in _scr_f_name for c in " \t\r\n[]."):
                st.error("❌ 公式名不能含：方括号、点、空白")
            else:
                # 不存在则写全局公式库（失败不影响筛选）
                try:
                    _exist = _cur_f.execute(
                        f"SELECT 1 FROM {ALIAS}.main.custom_metric_group_item "
                        f"WHERE group_id='GLOBAL_FORMULAS' AND display_name=?",
                        [_scr_f_name]).fetchone()
                    if not _exist:
                        _cur_f.execute(
                            f"INSERT INTO {ALIAS}.main.custom_metric_group_item "
                            "(group_id, item_order, item_type, formula, display_name, "
                            " value_type, display_type, unit, remark) "
                            "VALUES ('GLOBAL_FORMULAS', 0, 'formula', ?, ?, "
                            "        '期末值', '数字', '', '')",
                            [_scr_f_expr, _scr_f_name])
                        _invalidate_cf_cache()
                except Exception as _e:
                    st.warning(f"公式库写入失败（不影响本次筛选）：{_e}")

                _new = {
                    "cond_id": uuid.uuid4().hex[:8],
                    "table_name": "formula", "field_name": _scr_f_name,
                    "name_cn": _scr_f_name,
                    "time_mode": _scr_f_time,
                    "year": int(_scr_f_year) if _scr_f_time == "指定年份" else None,
                    "quarter": int(_scr_f_q) if _scr_f_time == "指定年份" else None,
                    "expr_type": "t",
                    "unit": _scr_f_unit, "min": _scr_f_min, "max": _scr_f_max,
                }
                _new_sig = _cond_signature(_new)
                if any(_cond_signature(c) == _new_sig for c in st.session_state.scr_conditions):
                    st.warning(f"⚠️ 已存在完全相同条件的行：{_cond_label(_new)}")
                else:
                    st.session_state.scr_conditions.append(_new)
                    st.rerun()

    if "scr_edit_idx" in st.session_state:
        _edit_condition_dialog(con, st.session_state["scr_edit_idx"])

    # ====== 3. 操作按钮 ======
    st.divider()
    # 落库表（首次运行时建）
    try:
        con.cursor().execute(
            f"CREATE TABLE IF NOT EXISTS {ALIAS}.main.screener ("
            "screener_id VARCHAR, name VARCHAR, owner_id VARCHAR, "
            "is_public BOOLEAN, payload_json VARCHAR, updated_at TIMESTAMP)")
    except Exception:
        pass

    with st.expander("📂 加载已保存的筛选器", expanded=False):
        try:
            _scr_list = con.cursor().execute(
                f"SELECT screener_id, name, updated_at FROM {ALIAS}.main.screener "
                f"ORDER BY updated_at DESC LIMIT 50"
            ).df()
        except Exception:
            _scr_list = pd.DataFrame()

        if _scr_list.empty:
            st.caption("暂无已保存的筛选器")
        else:
            _opt_map = {
                f"{r['name']}（{str(r['updated_at'])[:16]} · {str(r['screener_id'])[:6]}）":
                    r["screener_id"]
                for _, r in _scr_list.iterrows()
            }
            c_load1, c_load2 = st.columns([4, 1])
            with c_load1:
                _pick = st.selectbox("选择要加载的筛选器", [""] + list(_opt_map),
                                     key="scr_load_pick")
            with c_load2:
                st.write("")
                if st.button("加载", key="scr_load_btn",
                             disabled=not _pick, width='stretch'):
                    _sid = _opt_map[_pick]
                    _row = con.cursor().execute(
                        f"SELECT name, payload_json FROM {ALIAS}.main.screener "
                        f"WHERE screener_id=?", [_sid]).fetchone()
                    _loaded_name = _row[0]
                    import json as _json
                    st.session_state.scr_conditions = _json.loads(_row[1])
                    st.session_state["scr_screener_id"] = _sid
                    st.session_state["scr_save_name"] = _loaded_name    # 👈 关键新增
                    st.rerun()

    _bc1, _bc2, _bc3, _bc4, _bc_saveas, _bc5, _bc6, _bc7 = st.columns([1, 1, 1, 1, 1, 1, 1, 1])
    with _bc1:
        _do_screen = st.button("🎯 开始筛选", type="primary",
                               width='stretch', key="scr_do")
    with _bc2:
        if st.button("🗑️ 清空条件", width='stretch', key="scr_clear"):
            st.session_state.scr_conditions = []
            st.session_state.pop("scr_result", None)
            st.session_state.pop("scr_screener_id", None)
            st.rerun()
    with _bc3:
        _scr_name = st.text_input("筛选器名称", value="未命名筛选",
                                  key="scr_save_name", label_visibility="collapsed",
                                  placeholder="筛选器名称")
    with _bc4:
        if st.button("💾 保存", width='stretch', key="scr_save_btn"):
            import json as _json
            _sid = st.session_state.get("scr_screener_id") or uuid.uuid4().hex[:12]
            _payload = _json.dumps(st.session_state.scr_conditions, ensure_ascii=False)
            try:
                con.cursor().execute(
                    f"DELETE FROM {ALIAS}.main.screener WHERE screener_id=?", [_sid])
                con.cursor().execute(
                    f"INSERT INTO {ALIAS}.main.screener VALUES (?,?,?,?,?,?)",
                    [_sid, _scr_name, "default", False, _payload,
                     datetime.now()])
                st.session_state["scr_screener_id"] = _sid
                st.toast(f"✅ 已保存：{_scr_name}", icon="💾")
                st.rerun()
            except Exception as _e:
                st.error(f"保存失败：{_e}")
    with _bc_saveas:
        if st.button("📋 另存为", width='stretch', key="scr_saveas_btn"):
            st.session_state["_scr_show_saveas"] = True
            st.rerun()

    if st.session_state.get("_scr_show_saveas"):
        _new_name = st.text_input("另存为新筛选器名称",
                                  value=f"{_scr_name}_副本",
                                  key="scr_saveas_name")
        _sa1, _sa2 = st.columns(2)
        with _sa1:
            if st.button("取消", key="scr_saveas_cancel",
                         width='stretch'):
                st.session_state["_scr_show_saveas"] = False
                st.rerun()
        with _sa2:
            if st.button("确定保存", type="primary", key="scr_saveas_ok",
                         width='stretch'):
                import json as _json2
                _sid2 = uuid.uuid4().hex[:12]
                _payload2 = _json2.dumps(st.session_state.scr_conditions,
                                         ensure_ascii=False)
                con.cursor().execute(
                    f"INSERT INTO {ALIAS}.main.screener VALUES (?,?,?,?,?,?)",
                    [_sid2, _new_name, "default", False, _payload2,
                     datetime.now()])
                st.session_state["_scr_show_saveas"] = False
                st.toast(f"✅ 已另存为：{_new_name}", icon="📋")
                st.rerun()
    with _bc5:
        _test_c = st.text_input("测试公司代码", key="scr_test_code",
                                label_visibility="collapsed",
                                placeholder="测试目标股（代码）")
        _test_btn = st.button("🧪 测试目标股", width='stretch',
                              key="scr_test_btn", disabled=not _test_c)
    with _bc6:
        if st.session_state.scr_conditions:
            _df_cond = pd.DataFrame(st.session_state.scr_conditions)
            st.download_button(
                "💾 导出条件",
                data=_df_cond.to_csv(index=False).encode("utf-8-sig"),
                file_name=f"screener_conditions_{datetime.now():%Y%m%d_%H%M%S}.csv",
                mime="text/csv", key="scr_dl_cond",
                width='stretch')
    with _bc7:
        _up_cond = st.file_uploader("导入条件 CSV", type=["csv"],
                                     key="scr_up_cond", label_visibility="collapsed")
        if _up_cond is not None:
            _fid = getattr(_up_cond, "file_id", None) or id(_up_cond)
            if st.session_state.get("scr_up_cond_last_fid") != _fid:
                st.session_state["scr_up_cond_last_fid"] = _fid
                try:
                    _df_imp = pd.read_csv(_up_cond, dtype=str).fillna("")
                    def _num(x):
                        try:
                            return float(x) if str(x).strip() not in ("", "nan") else None
                        except Exception:
                            return None
                    _new_conds = []
                    for _, _r in _df_imp.iterrows():
                        _new_conds.append({
                            "cond_id": uuid.uuid4().hex[:8],
                            "table_name": _r.get("table_name", ""),
                            "field_name": _r.get("field_name", ""),
                            "name_cn": _r.get("name_cn", ""),
                            "time_mode": _r.get("time_mode", "最新财报"),
                            "year": int(float(_r["year"])) if str(_r.get("year", "")).strip() not in ("", "nan") else None,
                            "quarter": int(float(_r["quarter"])) if str(_r.get("quarter", "")).strip() not in ("", "nan") else None,
                            "expr_type": _r.get("expr_type", "t"),
                            "unit": _r.get("unit", "壹"),
                            "min": _num(_r.get("min", "")),
                            "max": _num(_r.get("max", "")),
                        })
                    st.session_state.scr_conditions = _new_conds
                    st.session_state.pop("scr_result", None)
                    st.success(f"导入 {len(_new_conds)} 条条件")
                    st.rerun()
                except Exception as _e:
                    st.error(f"导入失败: {_e}")

    def _eval_formula_for_screener(cur, formula_name, comp_list, time_mode, year, quarter):
        """给筛选器用：对一批公司在指定时间上跑一个自定义公式。返回 DataFrame[stock_code, value]"""
        if not comp_list:
            return pd.DataFrame()

        # 1. 找公式定义（优先全局库）
        try:
            _row = cur.execute(
                f"SELECT formula FROM {ALIAS}.main.custom_metric_group_item "
                f"WHERE group_id='GLOBAL_FORMULAS' AND item_type='formula' AND display_name=? "
                f"LIMIT 1",
                [formula_name],
            ).fetchone()
        except Exception:
            _row = None
        if not _row or not _row[0]:
            raise ValueError(f"公式「{formula_name}」未找到定义")
        _formula_expr = _row[0]

        if time_mode == "最新时间":
            raise ValueError(
                "自定义公式不支持『最新时间』，请选择『最新财报』或『指定年份』")

        _formula_defs = _cached_formula_defs(con)

        # 3. 递归解析底层表 + 最大回溯年数（← 关键修复 1）
        # —— 用字段复合键替代表名过滤 ——
        _base_fields = sorted(_collect_formula_base_fields_recursive(
            _formula_expr, _formula_defs))
        if not _base_fields:
            raise ValueError(f"公式「{formula_name}」依赖链中未引用任何底层字段")
        _max_n_years = max(_collect_formula_max_years_recursive(
            _formula_expr, _formula_defs), 1)
        _stock_ph = ",".join(["?"] * len(comp_list))

        if time_mode == "指定年份":
            _y = int(year or 2024)
            _rp = _y * 100 + int(quarter or 4) * 3
            _prev_q_rp = _prev_quarter_period(_rp)
            _rp_list = [
                _rp, _rp - 100, _rp - 200,
                _prev_q_rp,                       # 上一季度
                _prev_q_rp - 100,                 # ttm@prev_q 的上年同期（ttm_c2c 间接依赖）
                (_y - 1) * 100 + 12,              # 上年年报
                (_y - 2) * 100 + 12,              # 前年年报（ttm_y2y 间接依赖）
            ]
            for n in range(1, _max_n_years + 1):
                _rp_list.append(_rp - n * 100)
            _rp_list = list(dict.fromkeys(_rp_list))
            _rp_ph = ",".join(["?"] * len(_rp_list))
            _field_pairs_ph = ",".join(["(?,?)"] * len(_base_fields))
            _field_flat = [x for pair in _base_fields for x in pair]

            _sql = f"""
                SELECT stock_code, table_name, field_name,
                       report_period, expr_type, value
                FROM {TABLE}
                WHERE granularity <> 'latest'
                  AND stock_code IN ({_stock_ph})
                  AND report_period IN ({_rp_ph})
                  AND (table_name, field_name) IN ({_field_pairs_ph})
            """
            _params = list(comp_list) + list(_rp_list) + _field_flat

        else:  # 最新财报
            _fin_fields     = [p for p in _base_fields if p[0] not in ("hm", "pm")]
            _non_fin_fields = [p for p in _base_fields if p[0] in ("hm", "pm")]

            _fin_field_ph = (",".join(["(?,?)"] * len(_fin_fields))
                             if _fin_fields else "NULL")
            _non_fin_field_ph = (",".join(["(?,?)"] * len(_non_fin_fields))
                                 if _non_fin_fields else "NULL")
            _fin_flat     = [x for p in _fin_fields     for x in p]
            _non_fin_flat = [x for p in _non_fin_fields for x in p]

            _non_fin_sql = ""
            if _non_fin_fields:
                _non_fin_sql = f"""
                UNION ALL
                SELECT f.stock_code, f.table_name, f.field_name,
                       l.rp AS report_period, 't' AS expr_type, f.value
                FROM {TABLE} f
                JOIN latest l ON f.stock_code = l.stock_code
                WHERE f.granularity = 'latest'
                  AND (f.table_name, f.field_name) IN ({_non_fin_field_ph})
                """

            _sql = f"""
                WITH latest AS (
                    SELECT stock_code, MAX(report_period) AS rp
                    FROM {TABLE}
                    WHERE stock_code IN ({_stock_ph})
                      {"AND (table_name, field_name) IN (" + _fin_field_ph + ")" if _fin_fields else "AND granularity = 'latest'"}
                    GROUP BY stock_code
                ),
                offsets AS (
                    SELECT unnest(range(0, {_max_n_years + 1})) AS n
                ),
                target_periods AS (
                    SELECT l.stock_code, l.rp - o.n * 100 AS rp
                    FROM latest l CROSS JOIN offsets o
                    UNION
                    SELECT l.stock_code, l.rp - 200 AS rp FROM latest l
                    UNION
                    SELECT l.stock_code,
                           CAST(l.rp / 100 AS INT) * 100 - 100 + 12 AS rp
                    FROM latest l
                    UNION
                    SELECT l.stock_code,
                           CASE
                             WHEN l.rp % 100 = 3  THEN CAST(l.rp / 100 AS INT) * 100 - 100 + 12
                             WHEN l.rp % 100 = 6  THEN CAST(l.rp / 100 AS INT) * 100 + 3
                             WHEN l.rp % 100 = 9  THEN CAST(l.rp / 100 AS INT) * 100 + 6
                             WHEN l.rp % 100 = 12 THEN CAST(l.rp / 100 AS INT) * 100 + 9
                             ELSE l.rp - 3
                           END AS rp
                    FROM latest l
                    UNION
                    SELECT l.stock_code,
                           CAST(l.rp / 100 AS INT) * 100 - 200 + 12 AS rp
                    FROM latest l
                    UNION
                    SELECT l.stock_code,
                           CASE
                             WHEN l.rp % 100 = 3  THEN CAST(l.rp / 100 AS INT) * 100 - 200 + 12
                             WHEN l.rp % 100 = 6  THEN CAST(l.rp / 100 AS INT) * 100 - 100 + 3
                             WHEN l.rp % 100 = 9  THEN CAST(l.rp / 100 AS INT) * 100 - 100 + 6
                             WHEN l.rp % 100 = 12 THEN CAST(l.rp / 100 AS INT) * 100 - 100 + 9
                             ELSE l.rp - 103
                           END AS rp
                    FROM latest l
                ),
                fin_data AS (
                    SELECT f.stock_code, f.table_name, f.field_name,
                           f.report_period, f.expr_type, f.value
                    FROM {TABLE} f
                    JOIN target_periods t
                      ON f.stock_code = t.stock_code AND f.report_period = t.rp
                    WHERE f.granularity <> 'latest'
                      {"AND (f.table_name, f.field_name) IN (" + _fin_field_ph + ")" if _fin_fields else "AND FALSE"}
                )
                SELECT * FROM fin_data
                {_non_fin_sql}
            """
            _params = list(comp_list)
            if _fin_fields:     _params.extend(_fin_flat)     # latest CTE
            if _fin_fields:     _params.extend(_fin_flat)     # fin_data
            if _non_fin_fields: _params.extend(_non_fin_flat) # non_fin_sql

        _df_raw = cur.execute(_sql, _params).df()
        if _df_raw.empty:
            return pd.DataFrame()

        # 4. 构建 mini pivot
        _mini_pivot = {}
        for _sc, _tb, _fn, _p, _et, _v in zip(
            _df_raw["stock_code"], _df_raw["table_name"], _df_raw["field_name"],
            _df_raw["report_period"], _df_raw["expr_type"], _df_raw["value"],
        ):
            _sc = _safe_str(_sc); _tb = _safe_str(_tb); _fn = _safe_str(_fn)
            _p = int(_p)
            _et = _safe_str(_et) or "t"
            _key = f"{_tb}.{_fn}"
            _pivot_set(_mini_pivot, _key, _sc, _p, _et, {"value": _v, "raw": None})

        # 5. 递归展开公式依赖链（支持任意层嵌套 A→B→C→…）
        _ref_formula_names = set()
        _pending = [(formula_name, _formula_expr)]
        _seen_names = {formula_name}
        while _pending:
            _cur_name, _cur_expr = _pending.pop()
            for _m in _FORMULA_REF_RE.finditer(_cur_expr or ""):
                _dep = _m.group(1)
                if _dep not in _seen_names and _dep in _formula_defs:
                    _seen_names.add(_dep)
                    _ref_formula_names.add(_dep)
                    _pending.append((_dep, _formula_defs[_dep]))

        # 6. expr_type 上下文：基于所有相关表达式（含依赖链）检测
        _all_exprs = "\n".join(
            [_formula_expr] + [_formula_defs[n] for n in _ref_formula_names]
        )
        _et_ctx = ("ttm" if re.search(r'\.\s*ttm\s*\]', _all_exprs)
                   else "c" if re.search(r'\.\s*(?:c|q2)\s*\]', _all_exprs)
                   else "t")
        _et_write = _et_ctx

        # 7. 收集所有需要计算的报告期 和 每家公司的"锚定期"
        _comp_period = {}
        _all_periods = set()
        for _sc, _p in zip(_df_raw["stock_code"], _df_raw["report_period"]):
            _sc = _safe_str(_sc); _p = int(_p)
            _all_periods.add(_p)
            _comp_period[_sc] = max(_comp_period.get(_sc, 0), _p)

        # 7.5 从 t/c 补算缺失派生指标（让 [formula.X.ttm] / [ps.oi.ttm] 等能取到）
        _fill_missing_expr_types(_mini_pivot, list(_all_periods),
                                  list(comp_list), "q")

        def _topo_formula_order(root_name, formula_defs):
            """返回 (order, cyclic)。cyclic=True 表示遍历中检测到环。"""
            visited, visiting, order, cyclic = set(), set(), [], False

            def _visit(name):
                nonlocal cyclic
                if name in visited:
                    return
                if name in visiting:
                    cyclic = True
                    return
                visiting.add(name)
                expr = formula_defs.get(name, "")
                for m in _FORMULA_REF_RE.finditer(expr or ""):
                    dep = m.group(1)
                    if dep in formula_defs:
                        _visit(dep)
                visiting.discard(name)
                visited.add(name)
                order.append(name)

            _visit(root_name)
            return order, cyclic

        # 8. 嵌套公式迭代求解（遍历所有拉回来的期，确保 .y5/.q1 有数据可用）
        _topo, _cyclic = _topo_formula_order(formula_name, _formula_defs)

        if not _cyclic:
            # ---- 1. 预计算每家公司的"有效期集合"（锚定期 + 全部回溯期）----
            _company_periods = {}
            for _sc in comp_list:
                _anchor = _rp if time_mode == "指定年份" else _comp_period.get(_sc)
                if _anchor is None:
                    continue
                _ps = {_anchor, _anchor - 200}
                for n in range(1, _max_n_years + 1):
                    _ps.add(_anchor - n * 100)
                _prev_q = _prev_quarter_period(_anchor)
                _ps.add(_prev_q)
                _ps.add(_prev_q - 100)
                _y = _anchor // 100
                _ps.add((_y - 1) * 100 + 12)
                _ps.add((_y - 2) * 100 + 12)
                
                _company_periods[_sc] = _ps

            # ---- 2. 拓扑序求解 ----
            for _fn_name in _topo:
                _fn_expr = _formula_defs[_fn_name]
                _is_root = (_fn_name == formula_name)

                if _is_root:
                    # 根层：只算锚定期
                    for _sc in comp_list:
                        _p = _rp if time_mode == "指定年份" else _comp_period.get(_sc)
                        if _p is None:
                            continue
                        _val_t = _eval_formula(_fn_expr, _mini_pivot, _p, _sc, expr_type="t")
                        _val_main = _val_t if _et_ctx == "t" else _eval_formula(
                            _fn_expr, _mini_pivot, _p, _sc, expr_type=_et_ctx)
                        
                        for _pk in (_fn_name, f"formula.{_fn_name}"):
                            _pivot_set(_mini_pivot, _pk, _sc, _p, "t", {"value": _val_t, "raw": None})
                            if _et_write != "t":
                                _pivot_set(_mini_pivot, _pk, _sc, _p, _et_write, {"value": _val_main, "raw": None})
                else:
                    # 依赖层：只算"锚定期 + 回溯期"
                    for _sc in comp_list:
                        for _p in _company_periods.get(_sc, ()):
                            _val_t = _eval_formula(_fn_expr, _mini_pivot, _p, _sc, expr_type="t")
                            _val_main = _val_t if _et_ctx == "t" else _eval_formula(
                                _fn_expr, _mini_pivot, _p, _sc, expr_type=_et_ctx)
                            
                            for _pk in (_fn_name, f"formula.{_fn_name}"):
                                _pivot_set(_mini_pivot, _pk, _sc, _p, "t", {"value": _val_t, "raw": None})
                                if _et_write != "t":
                                    _pivot_set(_mini_pivot, _pk, _sc, _p, _et_write, {"value": _val_main, "raw": None})
        else:
            _tasks = [(formula_name, _formula_expr)] + [
                (n, _formula_defs[n]) for n in _ref_formula_names if n in _formula_defs
            ]
            for _round in range(len(_ref_formula_names) + 2):
                _progressed = False
                for _fn_name, _fn_expr in _tasks:
                    for _sc in comp_list:
                        for _p in _all_periods:
                            _val_t = _eval_formula(
                                _fn_expr, _mini_pivot, _p, _sc, expr_type="t")
                            if _et_ctx == "t":
                                _val_main = _val_t
                            else:
                                _val_main = _eval_formula(
                                    _fn_expr, _mini_pivot, _p, _sc, expr_type=_et_ctx)

                            for _pk in (_fn_name, f"formula.{_fn_name}"):
                                bucket = (_mini_pivot.setdefault(_pk, {})
                                                      .setdefault(_sc, {})
                                                      .setdefault(_p, {}))

                                old_t = bucket.get("t")
                                if old_t is None or old_t.get("value") != _val_t:
                                    bucket["t"] = {"value": _val_t, "raw": None}
                                    _progressed = True

                                if _et_write != "t":
                                    old_m = bucket.get(_et_write)
                                    if old_m is None or old_m.get("value") != _val_main:
                                        bucket[_et_write] = {"value": _val_main, "raw": None}
                                        _progressed = True
                if not _progressed:
                    break

        # 9. 输出
        _out = []
        for _sc in comp_list:
            # 如果是“指定年份”模式，强制输出指定的 `_rp` 期的结果
            if time_mode == "指定年份":
                _p = _rp
            else:
                _p = _comp_period.get(_sc)
            
            if _p is None:
                continue
                
            _pdat = _mini_pivot.get(formula_name, {}).get(_sc, {}).get(_p, {})
            _cell = _pdat.get(_et_write) or _pdat.get("t") or _pdat.get("")
            _v = _cell_val(_cell) if _cell else None
            if _v is None:
                continue
            try:
                fv = float(_v)
                if pd.isna(fv):
                    continue
                _out.append({"stock_code": _sc, "value": float(_v)})
            except (TypeError, ValueError):
                continue

        return pd.DataFrame(_out)

    # ========== 筛选器专用：基础条件缺派生指标时动态补算 ==========
    _DERIVED_EXPR_TYPES = {
        "t_y2y", "t_c2c", "c_y2y", "c_c2c", "c_2y",
        "ttm", "ttm_y2y", "ttm_c2c",
    }

    def _compute_derived_for_screener(cur, table_name, field_name, target_et,
                                       comp_list, time_mode, year, quarter):
        """当数据库缺少 target_et 时，从 t/c 动态补算，返回 DataFrame[stock_code, value]。
           前提：caller 已确认 target_et ∈ _DERIVED_EXPR_TYPES 且目标公司在库里没值。"""
        if not comp_list or target_et not in _DERIVED_EXPR_TYPES:
            return pd.DataFrame()

        tab = table_name
        if tab == "fs_a":
            return pd.DataFrame()
        if tab == "bs" and target_et in ("c_y2y", "c_c2c", "c_2y",
                                         "ttm_y2y", "ttm_c2c"):
            return pd.DataFrame()

        # ---- 1) 确定每家公司的"目标期"，并收集所有需要拉回的期 ----
        comp_target = {}
        if time_mode == "指定年份":
            _rp = int(year or 2024) * 100 + int(quarter or 4) * 3
            comp_target = {c: _rp for c in comp_list}
        elif time_mode == "最新财报":
            _latest_period = scalar_cached(f"SELECT MAX(report_period) FROM {TABLE} WHERE granularity <> 'latest'") or 999912
            ph = ",".join(["?"] * len(comp_list))
            df_lat = cur.execute(
                f"SELECT stock_code, MAX(report_period) AS rp FROM {TABLE} "
                f"WHERE stock_code IN ({ph}) AND granularity <> 'latest' "
                f"AND table_name = ? AND field_name = ? AND report_period >= {int(_latest_period) - 100} GROUP BY stock_code",
                list(comp_list) + [table_name, field_name]
            ).df()
            if df_lat.empty:
                return pd.DataFrame()
            comp_target = {_safe_str(r["stock_code"]): int(r["rp"])
                           for _, r in df_lat.iterrows()}
        else:  # 最新时间 不支持派生补算（latest 本来就是快照）
            return pd.DataFrame()

        need_periods = set()
        for rp in comp_target.values():
            y = rp // 100
            _prev_q = _prev_quarter_period(rp)
            need_periods.update([
                rp, rp - 100, rp - 200,
                (y - 1) * 100 + 12,          # 上年年报（ttm 分子）
                (y - 2) * 100 + 12,          # 前年年报（ttm_y2y 依赖 ttm@rp-100）
                _prev_q,                      # 上一季度（ttm_c2c）
                _prev_q - 100,                # ttm@prev_q 需要的上年同期（ttm_c2c 的间接依赖）
            ])
        need_periods = sorted(need_periods)

        # ---- 2) 查 t / c 基础数据 ----
        ph_c = ",".join(["?"] * len(comp_list))
        ph_p = ",".join(["?"] * len(need_periods))
        df_base = cur.execute(
            f"SELECT stock_code, report_period, expr_type, value FROM {TABLE} "
            f"WHERE stock_code IN ({ph_c}) AND granularity <> 'latest' "
            f"AND table_name = ? AND field_name = ? "
            f"AND report_period IN ({ph_p}) "
            f"AND expr_type IN ('t','c')",
            list(comp_list) + [table_name, field_name] + need_periods
        ).df()
        if df_base.empty:
            return pd.DataFrame()

        # ---- 3) 构建 mini pivot ----
        key = f"{table_name}.{field_name}"
        mini = {key: {}}
        for sc, p, et, v in zip(df_base["stock_code"], df_base["report_period"],
                                 df_base["expr_type"], df_base["value"]):
            sc = _safe_str(sc); p = int(p); et = _safe_str(et) or "t"
            _pivot_set(mini, key, sc, p, et, {"value": v, "raw": None})

        # ---- 4) 复用透视表的补算函数 ----
        _fill_missing_expr_types(mini, need_periods, list(comp_list), "q")

        # ---- 5) 输出每家公司在"自己目标期"上的 target_et ----
        out = []
        for sc, rp in comp_target.items():
            pdat = mini.get(key, {}).get(sc, {}).get(rp, {})
            cell = pdat.get(target_et)
            if cell is None:
                continue
            v = _cell_val(cell)
            if v is None:
                continue
            try:
                fv = float(v)
                if pd.isna(fv):
                    continue
                out.append({"stock_code": sc, "value": fv})
            except (TypeError, ValueError):
                continue
        return pd.DataFrame(out)

    # ====== 4. 筛选逻辑 ======
    def _run_screener(con, conditions, target_codes=None):
        cur = con.cursor()
        if not conditions:
            return pd.DataFrame()
        
        try:
            _com_cols = {r[0] for r in cur.execute(f"DESCRIBE {COMPANY_TABLE}").fetchall()}
        except Exception:
            _com_cols = set()

        # === 市场筛选 ===
        _cw, _cp = [], []
        _scr_market = st.session_state.get("scr_market", "AB股市场")
        if _scr_market == "A股市场":
            _cw.append("market = 'a'")
        elif _scr_market == "B股市场":
            _cw.append("market = 'b'")

        if scr_mutual and "mutual_market" in _com_cols:
            _cw.append("mutual_market = TRUE")

        # 基础公司集（行业 / 省份）
        if scr_industries:
            _ph = ",".join(["?"] * len(scr_industries))
            _op = "NOT IN" if st.session_state.get("scr_ind_mode") == "排除" else "IN"
            _cw.append(f"industry {_op} ({_ph})")
            _cp.extend(scr_industries)
        if scr_provinces:
            _ph = ",".join(["?"] * len(scr_provinces))
            _op = "NOT IN" if st.session_state.get("scr_prov_mode") == "排除" else "IN"
            _cw.append(f"province {_op} ({_ph})")
            _cp.extend(scr_provinces)

        # 屏蔽/退市/ST 过滤（company 表有对应字段时走 SQL，没有则后面用名称前缀兜底）
        if st.session_state.get("scr_excl_bl") and "is_blacklist" in _com_cols:
            _cw.append("(is_blacklist IS NULL OR is_blacklist = FALSE)")
        if st.session_state.get("scr_excl_del") and "is_delisted" in _com_cols:
            _cw.append("(is_delisted IS NULL OR is_delisted = FALSE)")
        if st.session_state.get("scr_excl_st") and "is_st" in _com_cols:
            _cw.append("(is_st IS NULL OR is_st = FALSE)")
        if st.session_state.get("scr_only_st") and "is_st" in _com_cols:
            _cw.append("is_st = TRUE")

        _sql_com = f"SELECT stock_code, name, industry, province FROM {COMPANY_TABLE}"
        if _cw:
            _sql_com += " WHERE " + " AND ".join(_cw)
        try:
            _df_com = cur.execute(_sql_com, _cp).df()
        except Exception:
            _df_com = pd.DataFrame()
        if _df_com.empty:
            return pd.DataFrame()

        _cand = set(_df_com["stock_code"].astype(str).tolist())

        if "is_st" not in _com_cols:
            def _is_st_name(code):
                name = COMPANY_NAME_MAP.get(_safe_str(code), "").strip()
                return name.startswith(("ST", "*ST", "SST", "S*ST"))

            if st.session_state.get("scr_excl_st"):
                _cand = {c for c in _cand if not _is_st_name(c)}
            if st.session_state.get("scr_only_st"):
                _cand = {c for c in _cand if _is_st_name(c)}

        if scr_bourse:
            _prefixes = tuple(
                p for b in scr_bourse for p in _A_BOURSE_PREFIXES.get(b, ())
            )
            if _prefixes:
                _cand = {c for c in _cand if c.startswith(_prefixes)}

        if target_codes is not None:                  # ← 新增 3 行
            _cand &= set(target_codes)

        _matched_by_cond = {}

        _latest_period = scalar_cached(f"SELECT MAX(report_period) FROM {TABLE} WHERE granularity <> 'latest'") or 999912
        for cond in conditions:
            if cond.get("hidden"):
                continue
            if not _cand:                       # ← 新增：候选为空立即退出，避免 IN () 语法错
                break

            _t, _f, _et = cond["table_name"], cond["field_name"], cond["expr_type"]

            if _t == "formula":
                try:
                    _df_val = _eval_formula_for_screener(
                        cur, _f, list(_cand),
                        cond["time_mode"], cond.get("year"), cond.get("quarter"),
                    )
                except Exception as _e:
                    st.warning(f"公式「{_f}」求值失败，该条件判定全部不通过: {_e}")
                    _cand = set(); break
            else:
                try:
                    _df_val = pd.DataFrame()
                    _in_sql    = "AND stock_code IN (" + ",".join(["?"] * len(_cand)) + ")"
                    _in_params = sorted(_cand)

                    if cond["time_mode"] == "最新财报":
                        _sql = f"""
                            WITH latest AS (
                                SELECT stock_code, MAX(report_period) AS rp
                                FROM {TABLE}
                                WHERE granularity <> 'latest'
                                  AND table_name = ? AND field_name = ?
                                  AND report_period >= {int(_latest_period) - 100}
                                  {_in_sql}
                                GROUP BY stock_code
                            )
                            SELECT f.stock_code, f.value
                            FROM {TABLE} f
                            JOIN latest l
                              ON f.stock_code = l.stock_code
                             AND f.report_period = l.rp
                            WHERE f.granularity <> 'latest'
                              AND f.table_name = ? AND f.field_name = ? AND f.expr_type = ?
                        """
                        _df_val = cur.execute(
                            _sql, [_t, _f] + _in_params + [_t, _f, _et]
                        ).df()

                    elif cond["time_mode"] == "指定年份":
                        _y  = int(cond["year"] or 2024)
                        _q  = int(cond["quarter"] or 4)
                        _rp = _y * 100 + _q * 3
                        _sql = f"""
                            SELECT stock_code, value FROM {TABLE}
                            WHERE table_name = ? AND field_name = ? AND expr_type = ?
                              AND granularity <> 'latest' AND report_period = ?
                              {_in_sql}
                        """
                        _df_val = cur.execute(
                            _sql, [_t, _f, _et, _rp] + _in_params
                        ).df()

                    elif cond["time_mode"] == "最新时间":
                        _sql = f"""
                            SELECT stock_code, value FROM {TABLE}
                            WHERE table_name = ? AND field_name = ?
                              AND granularity = 'latest'
                              {_in_sql}
                        """
                        _df_val = cur.execute(
                            _sql, [_t, _f] + _in_params
                        ).df()
                    else:
                        continue

                    # 派生指标补算：只对"候选里没拿到值"的公司补，用 _need 而非全部 _cand
                    if _et in _DERIVED_EXPR_TYPES:
                        _have = (set(_df_val["stock_code"].astype(str))
                                 if _df_val is not None and not _df_val.empty else set())
                        _need = [c for c in _cand if c not in _have]
                        if _need:
                            _df_derived = _compute_derived_for_screener(
                                cur, _t, _f, _et, _need,
                                cond["time_mode"], cond.get("year"), cond.get("quarter"),
                            )
                            if _df_derived is not None and not _df_derived.empty:
                                _df_val = (pd.concat([_df_val, _df_derived], ignore_index=True)
                                           if _df_val is not None and not _df_val.empty
                                           else _df_derived)
                except Exception as _e:
                    st.warning(f"条件「{_t}.{_f} [{_et}]」查询失败: {_e}")
                    continue

            if _df_val is None or _df_val.empty:
                _cand = set(); break

            # 单位 → 实际阈值，过滤逻辑保持原样
            _u = cond["unit"]
            def _to_actual(v):
                if v is None: return None
                v = float(v)
                if _u == "%":  return v / 100.0
                if _u == "亿": return v * 1e8
                if _u == "万": return v * 1e4
                return v
            _min_a, _max_a = _to_actual(cond["min"]), _to_actual(cond["max"])

            _vals = _df_val.set_index("stock_code")["value"]
            _mask = pd.Series([True] * len(_vals), index=_vals.index)
            if _min_a is not None: _mask &= (_vals >= _min_a)
            if _max_a is not None: _mask &= (_vals <= _max_a)

            _cand &= set(_vals.loc[_mask].index.astype(str))
            _matched_by_cond[cond["cond_id"]] = dict(
                zip(_df_val["stock_code"].astype(str), _df_val["value"])
            )

        if not _cand:
            return pd.DataFrame()

        _df_res = _df_com[_df_com["stock_code"].astype(str).isin(_cand)].copy()

        for _label, _vmap in _matched_by_cond.items():
            _df_res[_label] = _df_res["stock_code"].astype(str).map(_vmap)
        return _df_res

    if _do_screen:
        if not st.session_state.scr_conditions:
            st.warning("请先添加至少一个筛选条件")
        else:
            with st.spinner("正在筛选..."):
                _df_result = _run_screener(con, st.session_state.scr_conditions)
            st.session_state["scr_result"] = _df_result
            st.session_state.pop("scr_export_bytes", None)
            if _df_result is None or _df_result.empty:
                st.warning("没有公司满足所有条件。")
            else:
                st.success(f"✅ 找到 {len(_df_result)} 家公司")

    # _run_screener 定义完才处理"测试目标股"点击
    if _test_btn and _test_c:
        with st.spinner(f"测试 {_test_c}…"):
            _df_one = _run_screener(con, st.session_state.scr_conditions,
                                     target_codes={_test_c}) \
                if st.session_state.scr_conditions else pd.DataFrame()
        _hit = not _df_one.empty and _test_c in set(_df_one["stock_code"].astype(str))
        if _hit:
            st.success(f"✅ {_test_c} 通过全部条件")
        else:
            st.warning(f"❌ {_test_c} 未通过（可能不在候选范围，或某条件未命中）")

    # ====== 5. 结果展示 ======
    if "scr_result" in st.session_state:
        _df_res = st.session_state.scr_result
        if _df_res is None or _df_res.empty:
            st.info("筛选结果为 0。")
        else:
            _lat_time = scalar_cached(
                f"SELECT MAX(report_period) FROM {TABLE} WHERE granularity='latest'") or "—"
            _lat_q = scalar_cached(
                f"SELECT MAX(report_period) FROM {TABLE} "
                f"WHERE granularity<>'latest' AND table_name='ps'") or "—"
            st.markdown(
                f"##### 🏆 筛选结果（{len(_df_res)} 家） "
                f"<span style='color:#666;font-size:0.7em;'>"
                f"(最新时间: {_lat_time} · 最新季度: {_lat_q})</span>",
                unsafe_allow_html=True)
            _disp = _df_res.copy()
            _disp["公司"] = _disp["stock_code"].astype(str).map(
                lambda c: COMPANY_NAME_MAP.get(c, c) or c)

            _cid_to_label = {}
            for c in st.session_state.scr_conditions:
                if c.get("hidden"):
                    continue
                _cid = c.get("cond_id")
                _lbl = _cond_label(c)
                _et_lbl = EXPR_TYPE_LABELS.get(c["expr_type"], c["expr_type"])
                if c["time_mode"] == "指定年份":
                    _cid_to_label[_cid] = f"{_lbl} [{_et_lbl}]"
                else:
                    _tm_lbl = "最新财报" if c["time_mode"] == "最新财报" else "最新时间"
                    _cid_to_label[_cid] = f"{_lbl} [{_et_lbl}·{_tm_lbl}]"

            _cols = (["stock_code", "公司", "industry", "province"]
                     + [k for k in _cid_to_label if k in _disp.columns])
            _disp = _disp[_cols].rename(columns={
                "stock_code": "股票代码",
                "industry": "行业",
                "province": "省份",
                **_cid_to_label, # 注意：这里重命名后，列名变成了中文标签
            })

            # 隐藏列选择器（HTML 原版有）
            _all_cond_cols = [c for c in _disp.columns
                              if c not in ("股票代码", "公司", "行业", "省份")]
            with st.expander("👁️ 隐藏列", expanded=False):
                _hidden_cols = st.multiselect(
                    "选择要隐藏的列",
                    options=_all_cond_cols,
                    key="scr_hidden_cols")
            if _hidden_cols:
                _disp = _disp.drop(columns=_hidden_cols, errors="ignore")

            # ========= 修复：在这里基于重命名后的中文列名构建 _format_dict =========
            _format_dict = {}
            for c in st.session_state.scr_conditions:
                if c.get("hidden"):
                    continue
                _cid = c.get("cond_id")
                if _cid in _cid_to_label:
                    _col_name = _cid_to_label[_cid]
                    if _col_name in _disp.columns:  # 确保该列没有被用户隐藏
                        _u = c["unit"]
                        
                        # 使用闭包工厂函数，避免 Python 的延迟绑定问题
                        def _make_fmt(u=_u):
                            def _fmt(v):
                                if v is None or (isinstance(v, float) and pd.isna(v)):
                                    return "—"
                                try:
                                    fv = float(v)
                                except Exception:
                                    return str(v)
                                if u == "%":
                                    pct = fv * 100
                                    if abs(pct) >= 1000:
                                        return f"{fv:.2f}倍"
                                    return f"{pct:.2f}%"
                                if u == "亿": return f"{fv / 1e8:,.2f}"
                                if u == "万": return f"{fv / 1e4:,.2f}"
                                return f"{fv:,.2f}"
                            return _fmt
                        
                        _format_dict[_col_name] = _make_fmt()

            # 过滤掉已被隐藏的列，防止 Pandas Styler 找不到列而报错
            _format_dict = {k: v for k, v in _format_dict.items() if k in _disp.columns}

            # 使用 Styler 进行展示：底层依然是 float，点击表头时 Streamlit 会按真实数值排序
            if _format_dict:
                _styled_disp = _disp.style.format(_format_dict, na_rep="—")
                st.dataframe(_styled_disp, width='stretch', hide_index=True)
            else:
                st.dataframe(_disp, width='stretch', hide_index=True)
            if st.button("📦 准备导出结果", key="scr_prepare_export"):
                st.session_state["scr_export_bytes"] = _disp.to_csv(
                    index=False).encode("utf-8-sig")

            if "scr_export_bytes" in st.session_state:
                st.download_button(
                    "⬇️ 下载筛选结果 CSV",
                    data=st.session_state["scr_export_bytes"],
                    file_name=f"screener_result_{datetime.now():%Y%m%d_%H%M%S}.csv",
                    mime="text/csv")

@st.dialog("重命名分组")
def _rename_group_dialog(con, group_id, old_name):
    new_name = st.text_input("新名称", value=old_name, key="cf_new_group_name")
    c1, c2 = st.columns(2)
    with c1:
        if st.button("取消", key="cf_rename_cancel"):
            st.session_state["cf_show_rename"] = False
            st.rerun()
    with c2:
        if st.button("确定", type="primary", key="cf_rename_ok"):
            if new_name and new_name != old_name:
                con.cursor().execute(
                    f"UPDATE {ALIAS}.main.custom_metric_group SET group_name=? WHERE group_id=?",
                    [new_name, group_id])
            _invalidate_groups_cache()
            st.session_state["cf_show_rename"] = False
            st.rerun()

@st.dialog("新建分组")
def _create_group_dialog(con, table_name, owner_type, company_type):
    new_name = st.text_input("输入新分组名称（例如：利润分析、现金流质量）", key="cf_new_group_val")
    c1, c2 = st.columns(2)
    with c1:
        if st.button("取消", key="cf_create_cancel"):
            st.session_state["cf_show_create_group"] = False
            st.rerun()
    with c2:
        if st.button("确定", type="primary", key="cf_create_ok"):
            if new_name:
                gid = f"{company_type}_{table_name}_{owner_type}_{int(time.time())}"
                cur = con.cursor()
                cur.execute(
                    f"INSERT INTO {ALIAS}.main.custom_metric_group "
                    "(group_id, group_name, table_name, granularity, owner_type, sort_order, company_type) "
                    "VALUES (?,?,?,?,?,0,?)",
                    [gid, new_name, table_name, "any", owner_type, company_type])
                # 去掉 table_name = ? 的限制
                default_names = ["资产总计", "营业收入", "净利润", "经营活动产生的现金流量净额"]
                try:
                    q = f"SELECT DISTINCT table_name, field_name FROM {METRIC_TABLE} WHERE company_type = ? AND name_cn IN ({','.join(['?']*len(default_names))})"
                    params = [company_type] + default_names
                    for i, (t_name, f_name) in enumerate(cur.execute(q, params).fetchall()):
                        cur.execute(
                            f"INSERT INTO {ALIAS}.main.custom_metric_group_item "
                            "(group_id, item_order, item_type, table_name, field_name, formula, "
                            " display_name, additional_prefix, is_title, is_important, "
                            " value_type, display_type, unit, remark) "
                            "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                            [gid, i, "field", t_name, f_name, None, None, None,
                             False, False, "期末值", "数字", "", ""]
                        )
                except Exception:
                    pass
                _invalidate_groups_cache()
                st.session_state["cf_group_id_radio"] = gid
                st.session_state["cf_group_id"]       = gid
            st.session_state["cf_show_create_group"] = False
            st.rerun()

@st.dialog("删除分组")
def _delete_group_dialog(con, group_id, group_name):
    st.warning(f"⚠️ 确定要删除分组「{group_name}」吗？该操作不可逆，分组内的所有自定义指标配置将被清空。")
    c1, c2 = st.columns(2)
    with c1:
        if st.button("取消", key="cf_del_group_cancel"):
            st.session_state["cf_show_del_group"] = False
            st.rerun()
    with c2:
        if st.button("确定删除", type="primary", key="cf_del_group_ok"):
            cur = con.cursor()
            cur.execute(f"DELETE FROM {ALIAS}.main.custom_metric_group_item WHERE group_id=?", [group_id])
            cur.execute(f"DELETE FROM {ALIAS}.main.custom_metric_group WHERE group_id=?", [group_id])
            _cached_group_items.clear()
            _invalidate_groups_cache()
            if st.session_state.get("cf_group_id") == group_id:
                st.session_state.pop("cf_group_id", None)
                st.session_state.pop("cf_group_id_radio", None)
            st.session_state["cf_show_del_group"] = False
            st.rerun()

@st.dialog("批量删除分组", width="large")
def _batch_delete_groups_dialog(con, groups):
    """groups: [{'group_id':..., 'group_name':...}, ...]"""
    st.warning("⚠️ 批量删除不可逆，分组内的所有自定义指标配置会一并清空。")

    gid_map = {g["group_id"]: g["group_name"] for g in groups}
    all_ids = list(gid_map.keys())

    all_checked = st.checkbox(
        f"全选（共 {len(all_ids)} 个分组）", key="cf_batch_all")

    if all_checked:
        selected_ids = all_ids
        st.info("已全选：" + "、".join(gid_map[i] for i in all_ids))
    else:
        selected_ids = st.multiselect(
            "选择要删除的分组",
            options=all_ids,
            format_func=lambda gid: gid_map.get(gid, gid),
            key="cf_batch_sel")

    c1, c2 = st.columns(2)
    with c1:
        if st.button("取消", key="cf_batch_cancel", width='stretch'):
            st.session_state["cf_show_batch_del"] = False
            st.rerun()
    with c2:
        if st.button("确定删除", type="primary", key="cf_batch_ok",
                     width='stretch', disabled=not selected_ids):
            cur = con.cursor()
            for gid in selected_ids:
                cur.execute(
                    f"DELETE FROM {ALIAS}.main.custom_metric_group_item "
                    f"WHERE group_id=?", [gid])
                cur.execute(
                    f"DELETE FROM {ALIAS}.main.custom_metric_group "
                    f"WHERE group_id=?", [gid])
            _cached_group_items.clear()
            _invalidate_groups_cache()
            if st.session_state.get("cf_group_id") in selected_ids:
                st.session_state.pop("cf_group_id", None)
                st.session_state.pop("cf_group_id_radio", None)

            # ② 清掉 dialog 里 checkbox / multiselect 的残留状态
            st.session_state.pop("cf_batch_all", None)
            st.session_state.pop("cf_batch_sel", None)

            st.session_state["cf_show_batch_del"] = False
            st.rerun()

# ========== 数据显示设置模态框 ==========
@st.dialog("选择财务指标", width="large")
def _metric_settings_dialog(con, group_id, table_name, granularity, owner_type, company_type):
    cur = con.cursor()

    if st.session_state.pop("_dialog_just_closed", False):
        for k in list(st.session_state.keys()):
            if k.startswith("cb_") or k in (
                "ms_selected", "custom_tab_editor",
                "temp_items", "current_edit_gid",
                "f_name_input", "f_expr_input",
                "f_display", "f_unit", "cf_imp_csv",
                "_pending_f_expr", "_pending_clear_inputs",
                "_editing_formula_origin_name",   # ← 新增
                "_editing_formula_meta",      # ← 新增
                "cf_edit_formula_sel",            # ← 新增
                "cf_sort_sel",                    # ← 新增
                "_pending_sort_sel",   # ← 新增
                "cf_del_global_fname",
                "_items_changed",
            ):
                st.session_state.pop(k, None)
    type_labels = {"non_financial": "非金融", "bank": "银行", "insurance": "保险", "security": "证券", "reit": "房地产投资信托", "other_financial": "其他金融"}
    type_cn = type_labels.get(company_type, company_type)
    
    st.markdown(
        f"""<div style="background-color:#f8d7da; color:#842029; padding:12px; border-radius:6px; font-size:14px; border:1px solid #f5c2c7;">
        • 不同种类的财报(非金融、银行、保险、证券、房地产投资信托等等) 以及不同市场(CN, HK, US)都有着各自不同的配置。<u>您需要为不同种类的财报做不同的设置。</u><br>
        • 当前财报种类为：<strong>{type_cn}</strong>。
        </div>""", unsafe_allow_html=True)

    name_map = {}
    all_metrics = []
    try:
        _md_df = _cached_metric_dict(con, METRIC_TABLE)   # 已有 300s 缓存
        _filtered = _md_df[_md_df["company_type"] == company_type]
        for t, f, n in zip(_filtered["table_name"], _filtered["field_name"], _filtered["name_cn"]):
            if not pd.isna(t) and not pd.isna(f):
                name_map[(t, f)] = n if not pd.isna(n) else f
                all_metrics.append({"table_name": t, "field_name": f, "name_cn": name_map[(t, f)]})
    except Exception:
        pass

    if "temp_items" not in st.session_state or st.session_state.get("current_edit_gid") != group_id:
        raw_items = _cached_group_items(con, group_id)
        items = []
        for it in raw_items:
            items.append({
                "item_type": it.get("item_type", "field"),
                "table_name": it.get("table_name"),
                "field_name": it.get("field_name"),
                "formula": it.get("formula"),
                "display_name": it.get("display_name"),
                "value_type": it.get("value_type", "期末值"),
                "display_type": it.get("display_type", "数字"),
                "unit": it.get("unit", ""),
                "additional_prefix": it.get("additional_prefix"),
                "is_title": bool(it.get("is_title")),
                "is_important": bool(it.get("is_important")),
                "remark": it.get("remark", "")
            })
        st.session_state.temp_items = items
        st.session_state.current_edit_gid = group_id

    items = st.session_state.temp_items

    # ================= 🌟 新增：加载全局公式库 =================
    global_formulas = {}
    try:
        gdf = _cached_global_formulas(con)
        for _, r in gdf.iterrows():
            d = r.to_dict()
            if d.get("display_name"):
                global_formulas[d["display_name"]] = d

        _migrate_key = f"_formulas_migrated_{group_id}"
        if not st.session_state.get(_migrate_key):
            _migrated = False
            for it in items:
                if it["item_type"] == "formula":
                    fname = it.get("display_name") or it.get("formula")
                    if fname and fname not in global_formulas:
                        global_formulas[fname] = it
                        cur.execute(
                            f"DELETE FROM {ALIAS}.main.custom_metric_group_item "
                            f"WHERE group_id='GLOBAL_FORMULAS' AND display_name=?",
                            [fname])
                        cur.execute(
                            f"INSERT INTO {ALIAS}.main.custom_metric_group_item "
                            "(group_id, item_order, item_type, table_name, field_name, formula, "
                            " display_name, additional_prefix, is_title, is_important, "
                            " value_type, display_type, unit, remark) "
                            "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                            ['GLOBAL_FORMULAS', 0, 'formula', None, None,
                             it.get("formula"), fname, it.get("additional_prefix"),
                             bool(it.get("is_title")), bool(it.get("is_important")),
                             None, it.get("display_type"), it.get("unit"),
                             it.get("remark", "")])
                        _migrated = True
            st.session_state[_migrate_key] = True
            if _migrated:
                _cached_group_items.clear()
                _cached_global_formulas.clear()
    except Exception:
        pass
    # =========================================================

    # ================= 🌟 恢复原版：搜索框 =================
    all_map = {}
    for m in all_metrics:
        key = f"{m['table_name']}.{m['field_name']}"
        all_map[key] = f"{m['name_cn']} ({REPORT_TYPE_LABELS.get(m['table_name'], m['table_name'])})"

    # 🌟 修复：把当前已有的自定义公式也加入搜索选项，方便勾选/取消
    for it in items:
        if it["item_type"] == "formula":
            f_key = f"formula__{it.get('display_name') or it.get('formula')}"
            all_map[f_key] = f"[公式] {it.get('display_name') or it.get('formula')}"

    # 🌟 新增：把全局公式库加入搜索选项
    for fname, it in global_formulas.items():
        f_key = f"formula__{fname}"
        all_map[f_key] = f"[公式] {fname}"

    current_field_keys = []
    for it in items:
        if it["item_type"] == "field":
            current_field_keys.append(f"{it['table_name']}.{it['field_name']}")
        elif it["item_type"] == "formula":
            current_field_keys.append(f"formula__{it.get('display_name') or it.get('formula')}")

    current_field_keys_set = set(current_field_keys)

    if st.session_state.pop("_items_changed", False):
        st.session_state.ms_selected = list(current_field_keys)
        for _k in list(st.session_state.keys()):
            if _k.startswith("cf_metric_pick_"):
                st.session_state.pop(_k, None)
    elif "ms_selected" not in st.session_state:
        st.session_state.ms_selected = list(current_field_keys)

    ms_choices = st.multiselect(
        "🔍 搜索财务选项和指标（支持跨表多选）",
        options=list(all_map.keys()),
        format_func=lambda k: all_map.get(k, k),
        key="ms_selected"
    )

    ms_choices_set = set(ms_choices)
    
    # 🌟 修复：当搜索框发生变更时，同步处理底层字段和自定义公式
    if ms_choices_set != current_field_keys_set:
        new_items = []
        # 1. 保留用户还在搜索框里勾选着的项
        for it in items:
            if it["item_type"] == "field":
                if f"{it['table_name']}.{it['field_name']}" in ms_choices_set:
                    new_items.append(it)
            elif it["item_type"] == "formula":
                f_key = f"formula__{it.get('display_name') or it.get('formula')}"
                if f_key in ms_choices_set:
                    new_items.append(it)
                    
        # 2. 把新勾选的底层字段加进去（公式不能凭空加，只能在上面保留）
        for k in ms_choices_set - current_field_keys_set:
            if k.startswith("formula__"):     # ← 替换原来的 continue
                fname = k.replace("formula__", "")
                if fname in global_formulas:
                    gf = global_formulas[fname]
                    new_items.append({
                        "item_type": "formula",
                        "formula": gf.get("formula"),
                        "display_name": fname,
                        "display_type": gf.get("display_type") or "数字",
                        "unit": gf.get("unit") or "",
                        "additional_prefix": gf.get("additional_prefix"),
                        "is_title": bool(gf.get("is_title")),
                        "is_important": bool(gf.get("is_important")),
                        "remark": gf.get("remark") or ""
                    })
                continue
            t, f = k.split(".", 1)
            new_items.append({
                "item_type": "field", "table_name": t, "field_name": f,
                "value_type": "期末值", "display_type": "数字", "unit": "", "remark": ""
            })
            
        st.session_state.temp_items = new_items
        st.session_state["_items_changed"] = True
        st.rerun()

    # ================= 图1：指标排序标签区 =================
    st.markdown("<div style='color:#0d6efd; font-size:18px; margin-bottom:8px;'>指标排序</div>", unsafe_allow_html=True)
    tag_html = "<div style='border:1px solid #ccc; padding:10px; border-radius:6px; background:#fcfcfc; display:flex; flex-wrap:wrap; gap:8px; min-height:50px; max-height:100px; overflow-y:auto;'>"
    if not items:
        tag_html += "<span style='color:#999;'>暂无指标</span>"
    for it in items:
        if it["item_type"] == "field":
            nm = name_map.get((it["table_name"], it["field_name"]), it["field_name"])
        else:
            nm = it.get("display_name") or "自定义公式"
        tag_html += f"<span style='background:#198754; color:white; padding:4px 8px; border-radius:4px; font-size:13px;'>{nm}</span>"
    tag_html += "</div>"
    st.markdown(tag_html, unsafe_allow_html=True)

    items_field_set = {
        (it["table_name"], it["field_name"])
        for it in items if it["item_type"] == "field"
    }
    # ================= 按表浏览（虚拟滚动，只渲染一个 widget）=================
    _TAB_BY_TABLE = {"bs": "资产负债表", "ps": "利润表",
                     "cfs": "现金流量表", "m": "财务指标"}
    tab_names = list(_TAB_BY_TABLE.values()) + ["自定义指标"]

    _active_metric_tab = st.segmented_control(
        "表", tab_names, default=tab_names[0],
        key="cf_metric_active_tab", label_visibility="collapsed")
    if _active_metric_tab is None:          # 兜底：用户取消选中时回退第一项
        _active_metric_tab = tab_names[0]
    if _active_metric_tab == "自定义指标":
        with st.container():
            st.markdown("**已选指标详情**")
            
            # 🌟 修复：让表格显示所有项（包括普通字段和自定义公式）
            if not items:
                df_edit = pd.DataFrame(columns=["_anchor", "排序", "类型", "表名", "指标名", "ID/公式", "值类型"])
            else:
                df_edit = pd.DataFrame([{
                    "_anchor": idx,
                    "排序": idx + 1,
                    "类型": "公式" if it["item_type"] == "formula" else "字段",
                    "表名": "-" if it["item_type"] == "formula" else REPORT_TYPE_LABELS.get(it.get("table_name"), it.get("table_name")),
                    "指标名": (it.get("display_name") or "未命名公式") if it["item_type"] == "formula" else name_map.get((it.get("table_name"), it.get("field_name")), it.get("field_name")),
                    "公式内容": (it.get("formula") or "-") if it["item_type"] == "formula" else "-",
                    "ID/引用标签": (
                        f"[formula.{it.get('display_name') or '未命名'}.q4]"
                        if it["item_type"] == "formula"
                        else f"[{it.get('table_name')}.{it.get('field_name')}.q4]"
                    ),
                    "值类型": it.get("value_type", "期末值") if it["item_type"] == "field" else "-"
                } for idx, it in enumerate(items)])

            edited_df = st.data_editor(
                df_edit,
                column_config={
                    "_anchor": None,
                    "排序": st.column_config.NumberColumn(
                        "排序", min_value=1, step=1, width="small",
                        help="数字即位置；改完点下方【应用排序数字】生效（或用 ↑↓ 按钮）"),
                    "类型": st.column_config.TextColumn(disabled=True, width="small"),
                    "表名": st.column_config.TextColumn(disabled=True, width="small"),
                    "指标名": st.column_config.TextColumn(disabled=True, width="medium"),
                    "公式内容": st.column_config.TextColumn(disabled=True, width="large"),
                    "ID/引用标签": st.column_config.TextColumn(disabled=True, width="medium"),
                    "值类型": st.column_config.SelectboxColumn(options=["期初值", "期末值", "平均值", "TTM值", "-"])
                },
                num_rows="dynamic", hide_index=True, width='stretch', key="custom_tab_editor"
            )
            
            _row_map = {
                int(r["_anchor"]): r
                for _, r in edited_df.iterrows()
                if pd.notna(r.get("_anchor"))
            }
            # ---------- 处理：删行 / 值类型变更（不触发排序） ----------
            valid_anchors = set(edited_df["_anchor"].dropna().astype(int).tolist())
            new_items, changed = [], False
            for idx, it in enumerate(items):
                if idx not in valid_anchors:
                    changed = True
                    continue
                row_data = _row_map.get(idx)
                if row_data is None:
                    continue
                if it["item_type"] == "field" and it.get("value_type") != row_data["值类型"]:
                    it["value_type"] = row_data["值类型"]
                    changed = True
                new_items.append(it)

            if len(new_items) != len(items):
                st.session_state.temp_items = new_items
                st.session_state["_items_changed"] = True
                st.session_state.pop("custom_tab_editor", None)
                st.rerun()
            elif changed:
                st.session_state.temp_items = new_items

            # ---------- ↑↓ 按钮（平铺版，直接列出所有指标，一键移动） ----------
            # ---------- 批量删除已选指标（pills 标签版） ----------
            if items:
                _del_labels = []
                for _it in items:
                    if _it.get("item_type") == "formula":
                        _del_labels.append(f"[公式] {_it.get('display_name') or '未命名公式'}")
                    else:
                        _t = _it.get("table_name")
                        _f = _it.get("field_name")
                        _del_labels.append(name_map.get((_t, _f), _f))

                # pills 选中索引 —— 只做"标记"，不立刻删
                _del_sel = st.pills(
                    "🗑️ 点击要删除的指标（可多选）",
                    options=list(range(len(items))),
                    format_func=lambda i: f"{i+1}. {_del_labels[i]}",
                    selection_mode="multi",
                    key="cf_batch_del_pills",
                ) or []

                # 按钮确认删除
                if st.button(
                    f"🗑️ 删除选中的 {len(_del_sel)} 项",
                    disabled=not _del_sel,
                    key="cf_batch_del_items_btn",
                    width='content',
                ):
                    _del_set = set(_del_sel)
                    st.session_state.temp_items = [
                        it for i, it in enumerate(items) if i not in _del_set
                    ]
                    st.session_state["_items_changed"] = True
                    st.session_state.pop("custom_tab_editor", None)
                    st.session_state.pop("cf_batch_del_pills", None)
                    st.rerun()
            
            st.markdown("**调整顺序**")
            
            # 使用带边框的容器，如果指标多可以自带滚动条
            with st.container(height=260, border=True):
                for idx, it in enumerate(items):
                    # 获取指标的中文名/公式名
                    if it["item_type"] == "formula":
                        nm = f"{idx+1}. [公式] {it.get('display_name') or '未命名公式'}"
                    else:
                        t_name = it.get("table_name")
                        f_name = it.get("field_name")
                        nm = f"{idx+1}. {name_map.get((t_name, f_name), f_name)}"

                    # 每一行分三列：名称(占大头) + 上移按钮 + 下移按钮
                    r1, r2, r3, r4 = st.columns([7, 1, 1, 1])
                    with r1:
                        st.markdown(
                            f"<div style='padding-top: 5px; font-size: 14px; color: #333;'>{nm}</div>", 
                            unsafe_allow_html=True
                        )
                    with r2:
                        if st.button("▲ 上移", key=f"up_{idx}", disabled=(idx == 0), width='stretch'):
                            items[idx - 1], items[idx] = items[idx], items[idx - 1]
                            st.session_state.temp_items = items
                            st.session_state["_items_changed"] = True
                            st.session_state.pop("custom_tab_editor", None) # 刷新表格
                            st.rerun()
                    with r3:
                        if st.button("▼ 下移", key=f"down_{idx}", disabled=(idx == len(items) - 1), width='stretch'):
                            items[idx], items[idx + 1] = items[idx + 1], items[idx]
                            st.session_state.temp_items = items
                            st.session_state["_items_changed"] = True
                            st.session_state.pop("custom_tab_editor", None) # 刷新表格
                            st.rerun()
                    with r4:
                        if st.button("⧉ 复制", key=f"copy_{idx}", width='stretch'):
                            new_it = dict(items[idx])
                            if new_it.get("item_type") == "formula":
                                base = new_it.get("display_name") or "公式"
                                n = 2
                                exists = {
                                    it.get("display_name") for it in items
                                    if it.get("item_type") == "formula"
                                }
                                while f"{base}_copy{n}" in exists:
                                    n += 1
                                new_it["display_name"] = f"{base}_copy{n}"
                            items.insert(idx + 1, new_it)
                            st.session_state.temp_items = items
                            st.session_state["_items_changed"] = True
                            st.session_state.pop("custom_tab_editor", None)
                            st.rerun()

            # ---------- 应用数字排序（按钮触发，不自动） ----------
            if st.button("📋 应用排序数字", key="cf_apply_sort", width='content'):
                _sort_vals = {}
                for idx, it in enumerate(items):
                    row = _row_map.get(idx)
                    if row is None:
                        continue
                    sv = row["排序"]
                    try:
                        _sort_vals[idx] = float(sv) if pd.notna(sv) else float(idx + 1)
                    except Exception:
                        _sort_vals[idx] = float(idx + 1)
                if _sort_vals:
                    sorted_items = [it for idx, it in sorted(
                        zip(_sort_vals.keys(), items),
                        key=lambda x: (_sort_vals[x[0]], x[0]))]
                    if any(a is not b for a, b in zip(sorted_items, items)):
                        st.session_state.temp_items = sorted_items
                        st.session_state["_items_changed"] = True
                        st.session_state.pop("custom_tab_editor", None)
                        st.rerun()
                    else:
                        st.toast("顺序无变化")
                else:
                    st.toast("请先在「排序」列填数字")

            # 用 name 做 key（_name_ok 已保证同名唯一，排序不影响）
            formula_items_for_edit = [
                it.get("display_name") or f"未命名_{i+1}"
                for i, it in enumerate(items)
                if it["item_type"] == "formula"
            ]
            if formula_items_for_edit:
                # 🌟 改为 3 列：[下拉框] [载入编辑] [彻底删除]
                ec1, ec2, ec3 = st.columns([3, 1, 1])
                with ec1:
                    sel_edit_name = st.selectbox(
                        "✏️ 选择要编辑的已有公式",
                        options=formula_items_for_edit,
                        key="cf_edit_formula_sel",
                    )
                with ec2:
                    st.write(""); st.write("")
                    if st.button("载入编辑", key="cf_edit_formula_btn", width='stretch'):
                        for it in items:
                            if it["item_type"] == "formula" and (it.get("display_name") or "") == sel_edit_name:
                                st.session_state["f_name_input"] = it.get("display_name") or ""
                                st.session_state["f_expr_input"] = it.get("formula") or ""
                                disp = it.get("display_type") or "数字"
                                st.session_state["f_display"] = disp if disp in ("金额", "数字", "百分比") else "数字"
                                unit = it.get("unit") or ""
                                st.session_state["f_unit"] = unit if unit in ("", "亿", "百万", "万", "壹") else ""
                                st.session_state["_editing_formula_origin_name"] = it.get("display_name") or ""
                                st.session_state["_editing_formula_meta"] = {
                                    "additional_prefix": it.get("additional_prefix"),
                                    "is_title": bool(it.get("is_title")),
                                    "is_important": bool(it.get("is_important")),
                                    "remark": it.get("remark") or "",
                                }
                                st.rerun()
                with ec3:
                    st.write(""); st.write("")
                    # 🌟 新增：彻底删除按钮
                    if st.button("🗑️ 彻底删除", key="cf_del_global_btn", width='stretch'):
                        st.session_state["cf_del_global_fname"] = sel_edit_name
                        st.rerun()

                # 触发行内删除确认（不能嵌套 dialog）
                _del_fname = st.session_state.get("cf_del_global_fname")
                if _del_fname:
                    st.warning(f"⚠️ 确定要彻底删除全局公式「{_del_fname}」吗？这会同时从**所有分组**中移除该公式。如果其他公式引用了它，相应位置将显示 `--`。")
                    dc1, dc2 = st.columns(2)
                    with dc1:
                        if st.button("取消删除", key="cf_cancel_del_global", width='stretch'):
                            st.session_state.pop("cf_del_global_fname", None)
                            st.rerun()
                    with dc2:
                        if st.button("确定彻底删除", type="primary", key="cf_confirm_del_global", width='stretch'):
                            cur = con.cursor()
                            # 1. 从全局库删除
                            cur.execute(f"DELETE FROM {ALIAS}.main.custom_metric_group_item WHERE group_id='GLOBAL_FORMULAS' AND display_name=?", [_del_fname])
                            # 2. 从所有分组的 items 里全部删除（彻底销毁）
                            cur.execute(f"DELETE FROM {ALIAS}.main.custom_metric_group_item WHERE item_type='formula' AND display_name=?", [_del_fname])
                            _invalidate_cf_cache()
                            
                            # 3. 从当前 session 的 items 里移除
                            if "temp_items" in st.session_state:
                                st.session_state.temp_items = [
                                    it for it in st.session_state.temp_items 
                                    if not (it.get("item_type") == "formula" and it.get("display_name") == _del_fname)
                                ]
                            
                            st.session_state.pop("cf_del_global_fname", None)
                            st.session_state["_items_changed"] = True
                            st.rerun()

            # 只有普通字段才显示在快捷拼接按钮里
            field_items = [it for it in items if it["item_type"] == "field"]

            st.divider()
            st.markdown("**创建自定义公式**")
            _editing_origin = st.session_state.get("_editing_formula_origin_name")
            if _editing_origin:
                st.info(f"✏️ 正在编辑：{_editing_origin}（保存将原位替换；想新建请点【取消】退出重进）")
            st.info("复制指标的 ID 去进行：或(||)、加(+)、减(-)、乘(*)、除(/)、绝对值(abs)、平均值(avg)。 运算示例：`【指标1 || 0】`、`【abs(指标1 - 指标2)】`")
            
            col_form, col_desc = st.columns([1, 2])
            with col_form:
                if "_pending_f_expr" in st.session_state:
                    st.session_state["f_expr_input"] = st.session_state.pop("_pending_f_expr")
                if st.session_state.pop("_pending_clear_inputs", False):
                    st.session_state["f_name_input"] = ""
                    st.session_state["f_expr_input"] = ""
                f_name = st.text_input("公式名称", placeholder="新建指标", key="f_name_input")
                f_expr = st.text_area("公式 (可点击下方按钮拼接)", height=100, key="f_expr_input")

                def _append_formula_token(qit):
                    cur_expr = st.session_state.get("f_expr_input", "")
                    vt_suffix = {"期初值": "q1", "期末值": "q4", "平均值": "avg", "TTM值": "ttm"}.get(qit["value_type"], "q4")
                    new_id = f"[{qit['table_name']}.{qit['field_name']}.{vt_suffix}]"
                    st.session_state["_pending_f_expr"] = cur_expr + ("" if not cur_expr else " + ") + new_id

                quick_cols = st.columns(4)
                for qi, qit in enumerate(field_items[:8]):
                    with quick_cols[qi % 4]:
                        nm_short = name_map.get((qit["table_name"], qit["field_name"]), qit["field_name"])[:5]
                        st.button(f"+{nm_short}", key=f"qadd_{qi}",
                                  width='stretch',
                                  on_click=_append_formula_token, args=(qit,))

            with col_desc:
                if f_expr:
                    def repl(match):
                        tn = match.group(1).strip()
                        fn, vt = _split_field_vt(match.group(2))
                        if not fn:
                            return match.group(0)
                            
                        # 顺手补齐 t 和 c 的翻译
                        vt_map = {"t": "累计", "c": "单季", "q1": "期初值", "q4": "期末值", "avg": "平均值", "ttm": "TTM值"}
                        vt_label = vt_map.get(vt)
                        if vt_label is None and re.fullmatch(r"y\d+", vt):
                            vt_label = f"{vt[1:]}年前同期"
                        if vt_label is None:
                            vt_label = vt
                        if tn == "formula":
                            return f"{vt_label}「{fn}」（自定义公式）"
                        nm = name_map.get((tn, fn), fn)
                        return f"{vt_label} {nm}".strip()
                        
                    desc = re.sub(
                        r'\[\s*([^\s\[\].]+)\s*\.\s*([^\s\[\]]+?)\s*\]',
                        repl, f_expr)
                    st.markdown(f"<div style='background:#f8f9fa; padding:10px; border-radius:4px; font-size:14px;'>详情：{desc}</div>", unsafe_allow_html=True)
                
                st.write("数据显示类型")
                f_display = st.radio("显示类型", ["金额", "数字", "百分比"], horizontal=True, label_visibility="collapsed", key="f_display")
                st.write("单位")
                f_unit = st.radio("单位", ["", "亿", "百万", "万", "壹"], horizontal=True, label_visibility="collapsed", key="f_unit")
                
            # === 公式名校验：只有空白、方括号、点会破坏三段解析；其他字符都安全 ===
            _name_ok = True
            _editing_origin = st.session_state.get("_editing_formula_origin_name")
            if f_name and any(c in f_name for c in " \t\r\n[]."):
                st.error("❌ 公式名不能含：方括号、点、空白（其他字符均可，支持中文）")
                _name_ok = False
            elif f_name and (
                # 检查当前 items 里是否有重名
                any((it.get("display_name") or "") != (_editing_origin or "") and it["item_type"] == "formula" and (it.get("display_name") or "") == f_name for it in items)
                # 检查全局库里是否有重名
                or (f_name in global_formulas and f_name != (_editing_origin or ""))
            ):
                st.error(f"❌ 已存在同名公式「{f_name}」，请换个名字")
                _name_ok = False

            if st.button("保存公式指标", type="primary", key="save_formula_btn",
                         width='stretch',
                         disabled=not (f_name and f_expr and _name_ok)):
                # 🔧 取出暂存的元数据（新建时为空字典）
                _meta = st.session_state.pop("_editing_formula_meta", {}) or {}

                new_formula = {
                    "item_type": "formula",
                    "formula": f_expr,
                    "display_name": f_name,
                    "display_type": f_display,
                    "unit": f_unit,
                    # 🔧 沿用旧值，UI 没改就不动
                    "additional_prefix": _meta.get("additional_prefix"),
                    "is_title": bool(_meta.get("is_title", False)),
                    "is_important": bool(_meta.get("is_important", False)),
                    "remark": _meta.get("remark", ""),
                }
                edit_origin = st.session_state.pop("_editing_formula_origin_name", None)
                edit_idx = None
                if edit_origin:
                    for i, it in enumerate(items):
                        if it["item_type"] == "formula" and (it.get("display_name") or "") == edit_origin:
                            edit_idx = i
                            break
                if edit_idx is not None:
                    items[edit_idx] = new_formula       # 原位替换（排序也不会错位）
                else:
                    items.append(new_formula)
                if edit_origin and edit_origin != f_name:
                    cur.execute(f"DELETE FROM {ALIAS}.main.custom_metric_group_item WHERE group_id='GLOBAL_FORMULAS' AND display_name=?", [edit_origin])
                    
                cur.execute(f"DELETE FROM {ALIAS}.main.custom_metric_group_item WHERE group_id='GLOBAL_FORMULAS' AND display_name=?", [f_name])
                cur.execute(
                    f"INSERT INTO {ALIAS}.main.custom_metric_group_item "
                    "(group_id, item_order, item_type, table_name, field_name, formula, display_name, additional_prefix, is_title, is_important, value_type, display_type, unit, remark) "
                    "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                    ['GLOBAL_FORMULAS', 0, 'formula', None, None, f_expr, f_name, new_formula.get("additional_prefix"), new_formula.get("is_title"), new_formula.get("is_important"), None, f_display, f_unit, new_formula.get("remark", "")]
                )
                _invalidate_cf_cache()
                st.session_state.temp_items = items
                st.session_state["_items_changed"] = True
                st.session_state["_pending_clear_inputs"] = True
                st.rerun()

    elif _active_metric_tab:
        _tbl = next(k for k, v in _TAB_BY_TABLE.items() if v == _active_metric_tab)
        metrics = [m for m in all_metrics if m["table_name"] == _tbl]

        if not metrics:
            st.info("该表暂无数据")
        else:
            df_pick = pd.DataFrame([
                {"勾选": (m["table_name"], m["field_name"]) in items_field_set,
                 "_key": f"{m['table_name']}.{m['field_name']}",
                 "指标名": m["name_cn"],
                 "字段": m["field_name"]}
                for m in metrics
            ])
            edited_pick = st.data_editor(
                df_pick,
                hide_index=True, width='stretch', num_rows="fixed",
                key=f"cf_metric_pick_{_tbl}",
                column_config={
                    "勾选": st.column_config.CheckboxColumn("勾选", width="small"),
                    "_key": None,  # 隐藏
                    "指标名": st.column_config.TextColumn(disabled=True, width="large"),
                    "字段": st.column_config.TextColumn(disabled=True, width="medium"),
                },
            )
            # ---- diff 检测：相对当前 items 的变化 ----
            _orig_map = dict(zip(df_pick["_key"], df_pick["勾选"]))
            _new_map = dict(zip(edited_pick["_key"], edited_pick["勾选"]))
            _added_keys = {k for k, v in _new_map.items()
                           if v and not _orig_map.get(k, False)}
            _removed_keys = {k for k, v in _orig_map.items()
                             if v and not _new_map.get(k, False)}

            if _added_keys or _removed_keys:
                _new_items = [
                    it for it in items
                    if not (it["item_type"] == "field"
                            and f"{it['table_name']}.{it['field_name']}" in _removed_keys)
                ]
                for _k in _added_keys:
                    _t, _f = _k.split(".", 1)
                    _new_items.append({
                        "item_type": "field", "table_name": _t, "field_name": _f,
                        "value_type": "期末值", "display_type": "数字",
                        "unit": "", "remark": ""
                    })
                st.session_state.temp_items = _new_items
                st.session_state["_items_changed"] = True
                st.rerun()

    st.divider()
    
    # ================= 🌟 恢复原版：导入/导出/清空/恢复默认 =================
    c_imp, c_exp, c_clear, c_reset, c_reset_preview = st.columns(5)
    with c_imp:
        up = st.file_uploader(
            "导入CSV", type=["csv"], key="cf_imp_csv",
            label_visibility="collapsed",
        )
        if up is not None:                                    # ← 显式 is not None
            _fid = getattr(up, "file_id", None) or id(up)     # ← 新增
            if st.session_state.get("cf_imp_last_fid") != _fid:   # ← 新增
                st.session_state["cf_imp_last_fid"] = _fid        # ← 新增
                import io as _io
                _raw = up.getvalue().decode("utf-8-sig")
                _existing = {
                    f"{it.get('table_name')}.{it.get('field_name')}"
                    for it in items if it.get("item_type") == "field"
                }
                _added = 0

                # 判断是否新格式：首行含 item_type 或 field_name 列
                _first = next((l for l in _raw.splitlines() if l.strip()), "")
                _is_new = ("item_type" in _first) or ("field_name" in _first)

                if _is_new:
                    _df_imp = pd.read_csv(_io.StringIO(_raw), dtype=str).fillna("")
                    _need_invalidate = False
                    for _, r in _df_imp.iterrows():
                        _itype = (r.get("item_type") or "field").strip().lower()
                        if _itype == "formula":
                            _f = (r.get("formula") or "").strip()
                            _dn = (r.get("display_name") or "").strip()
                            if not _f or not _dn:
                                continue
                            # 非法字符校验
                            if any(c in _dn for c in " \t\r\n[]."):
                                st.warning(f"跳过公式「{_dn}」：名称不能含空格/方括号/点")
                                continue
                            # 当前 items + 全局库去重
                            _exist_f = {
                                it.get("display_name") for it in items
                                if it.get("item_type") == "formula"
                            } | set(global_formulas.keys())
                            if _dn in _exist_f:
                                st.warning(f"跳过公式「{_dn}」：已存在同名公式")
                                continue
                            # 写全局库
                            cur.execute(
                                f"DELETE FROM {ALIAS}.main.custom_metric_group_item "
                                f"WHERE group_id='GLOBAL_FORMULAS' AND display_name=?",
                                [_dn],
                            )
                            cur.execute(
                                f"INSERT INTO {ALIAS}.main.custom_metric_group_item "
                                "(group_id, item_order, item_type, table_name, field_name, formula, "
                                " display_name, additional_prefix, is_title, is_important, "
                                " value_type, display_type, unit, remark) "
                                "VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?)",
                                ['GLOBAL_FORMULAS', 0, 'formula', None, None, _f, _dn,
                                 (r.get("additional_prefix") or "").strip() or None,
                                 str(r.get("is_title", "")).lower() in ("1", "1.0", "true", "yes"),
                                 str(r.get("is_important", "")).lower() in ("1", "1.0", "true", "yes"),
                                 None,
                                 (r.get("display_type") or "数字").strip() or "数字",
                                 (r.get("unit") or "").strip(),
                                 (r.get("remark") or "").strip()],
                            )
                            _need_invalidate = True
                            items.append({
                                "item_type": "formula",
                                "formula": _f,
                                "display_name": _dn,
                                "display_type": (r.get("display_type") or "数字").strip() or "数字",
                                "unit": (r.get("unit") or "").strip(),
                                "additional_prefix": (r.get("additional_prefix") or "").strip() or None,
                                "is_title": str(r.get("is_title", "")).lower() in ("1", "1.0", "true", "yes"),
                                "is_important": str(r.get("is_important", "")).lower() in ("1", "1.0", "true", "yes"),
                                "remark": (r.get("remark") or "").strip(),
                            })
                            _added += 1
                        else:
                            _t = (r.get("table_name") or "").strip() or table_name
                            _f = (r.get("field_name") or "").strip()
                            if not _f:
                                continue
                            _k = f"{_t}.{_f}"
                            if _k in _existing:
                                continue
                            items.append({
                                "item_type": "field",
                                "table_name": _t,
                                "field_name": _f,
                                "value_type": (r.get("value_type") or "期末值").strip() or "期末值",
                                "display_type": (r.get("display_type") or "数字").strip() or "数字",
                                "unit": (r.get("unit") or "").strip(),
                                "additional_prefix": (r.get("additional_prefix") or "").strip() or None,
                                "is_title": str(r.get("is_title", "")).lower() in ("1", "1.0", "true", "yes"),
                                "is_important": str(r.get("is_important", "")).lower() in ("1", "1.0", "true", "yes"),
                                "remark": (r.get("remark") or "").strip(),
                            })
                            _existing.add(_k)
                            _added += 1
                    if _need_invalidate:                               # ← 循环外，一次性
                        _invalidate_cf_cache()
                else:
                    # 旧格式：每行 field_name 或 table.field
                    for line in _io.StringIO(_raw):
                        line = line.strip()
                        if not line:
                            continue
                        _KNOWN_TABLES = {"bs","ps","cfs","m","fs_a","hm","pm"}
                        if "." in line:
                            _t0, _f0 = line.split(".", 1)
                            if _t0 in _KNOWN_TABLES:
                                _t, _f = _t0, _f0
                            else:
                                _t, _f = table_name, line
                        else:
                            _t, _f = table_name, line
                        _k = f"{_t}.{_f}"
                        if _t and _f and _k not in _existing:
                            items.append({
                                "item_type": "field",
                                "table_name": _t,
                                "field_name": _f,
                                "value_type": "期末值",
                                "display_type": "数字",
                                "unit": "",
                                "remark": "",
                            })
                            _existing.add(_k)
                            _added += 1

                if _added:
                    _cached_group_items.clear()
                    st.session_state.temp_items = items
                    st.session_state["_items_changed"] = True
                    st.session_state.pop("custom_tab_editor", None)
                    st.rerun()
                else:
                    st.toast("文件里没有新指标（可能都已存在或 CSV 为空）")
            
    with c_exp:
        _exp_rows = []
        for it in items:
            _exp_rows.append({
                "display_name": it.get("display_name", "") or "",
                "item_type": it.get("item_type", "field"),
                "table_name": it.get("table_name", "") or "",
                "field_name": it.get("field_name", "") or "",
                "formula": it.get("formula", "") or "",
                "value_type": it.get("value_type", "期末值") or "期末值",
                "display_type": it.get("display_type", "数字") or "数字",
                "unit": it.get("unit", "") or "",
                "additional_prefix": it.get("additional_prefix", "") or "",
                "is_title": bool(it.get("is_title")),
                "is_important": bool(it.get("is_important")),
                "remark": it.get("remark", "") or "",
            })
        _exp_df = pd.DataFrame(_exp_rows)
        st.download_button(
            "导出CSV",
            data=_exp_df.to_csv(index=False).encode("utf-8-sig"),
            file_name=f"{group_id}_metrics.csv",
            key="cf_exp_csv",
            width='stretch',
        )
    with c_clear:
        if st.button("清空指标", key="cf_del_all", width='stretch'):
            st.session_state.temp_items = []
            st.session_state["_items_changed"] = True
            st.rerun()
            
    with c_reset:
        if st.button("恢复系统默认", key="cf_reset_default", width='stretch'):
            cur.execute(f"DELETE FROM {ALIAS}.main.custom_metric_group_item WHERE group_id=?", [group_id])
            try:
                for group_name, tabs, fields in DEFAULT_GROUPS:
                    if not tabs or tabs[0] != table_name:
                        continue
                    # ← 改为收集后一次性批量插入
                    _rows = [
                        [group_id, i, "field", table_name, fn,
                         None, None, None, False, False, "期末值", "数字", "", ""]
                        for i, fn in enumerate(fields)
                    ]
                    if _rows:
                        _ph = "(" + ",".join(["?"] * 14) + ")"
                        cur.execute(
                            f"INSERT INTO {ALIAS}.main.custom_metric_group_item "
                            f"(group_id, item_order, item_type, table_name, field_name, formula, "
                            f" display_name, additional_prefix, is_title, is_important, "
                            f" value_type, display_type, unit, remark) "
                            f"VALUES " + ",".join([_ph] * len(_rows)),
                            [x for row in _rows for x in row])
                    break
            except Exception:
                pass
            _cached_group_items.clear()
            _cached_formula_defs.clear()
            st.session_state.pop("temp_items", None)
            st.session_state["_items_changed"] = True
            st.rerun()

    with c_reset_preview:
        if st.button("↩️ 重置（不保存，回到 DB 状态）", key="cf_reset_preview"):
            st.session_state.pop("temp_items", None)
            st.session_state["_items_changed"] = True
            st.rerun()

    st.divider()
    
    # ================= 取消 / 确定 =================
    btn_cols = st.columns([1, 1])
    with btn_cols[0]:
        if st.button("取消", key="cf_dlg_cancel", width='stretch'):
            st.session_state["cf_show_metric_dialog"] = False
            st.session_state["_dialog_just_closed"] = True
            st.rerun()
    with btn_cols[1]:
        if st.button("确定", type="primary", key="cf_dlg_ok", width='stretch'):
            _save_group_items(cur, group_id, items)
            st.session_state["cf_show_metric_dialog"] = False
            st.session_state["_dialog_just_closed"] = True
            _invalidate_cf_cache()
            st.rerun()

def _cf_build_L2(cur, sel_comps, comp_head, granularity, owner_type,
                 start_period, end_period, group_id, report_type,
                 page_index, page_size, expr_types_needed,
                 group_items, sel_table, sel_company_type, con=None, hide_empty=False, show_types=None):
    """L2 快照：分页 + 主查询 + 审计 + 链接 + 公式。只在 L2 key 变化时调用。"""

    # ---------- 分页 SQL ----------
    month_filter, month_params = "", []
    if report_type != "全部":
        month_map = {"一季报": "03", "中报": "06", "三季报": "09", "年报": "12"}
        month_filter = " AND substr(CAST(report_period AS VARCHAR),5,2) = ? "
        month_params = [month_map[report_type]]

    if granularity == "latest":
        pdf = cur.execute(
            f"SELECT DISTINCT report_period FROM {TABLE} "
            f"WHERE stock_code = ? AND granularity = 'latest'", [comp_head]).df()
        periods = [int(p) for p in pdf["report_period"].tolist()]
        total_periods, max_page, page_index = len(periods), 0, 0
    else:
        try:
            total_periods = _cached_total_periods(
                con if con is not None else cur, comp_head, granularity, owner_type,
                start_period, end_period, report_type)
        except Exception:
            total_periods = 0
        max_page = max(0, (total_periods - 1) // page_size) if total_periods else 0
        page_index = min(max(page_index, 0), max_page)
        offset = page_index * page_size
        try:
            pdf = cur.execute(
                f"SELECT DISTINCT report_period FROM {TABLE} "
                f"WHERE stock_code = ? AND granularity = ? AND owner_type = ? "
                f"AND report_period >= ? AND report_period <= ? {month_filter} "
                f"ORDER BY report_period DESC LIMIT ? OFFSET ?",
                [comp_head, granularity, owner_type, start_period, end_period]
                + month_params + [page_size, offset]).df()
            periods = [int(p) for p in pdf["report_period"].tolist()]
        except Exception:
            periods = []

    if not periods:
        return dict(periods=[], pivot={}, field_order=[], audit_tip_map={},
                    period_links={}, items_meta={}, total_periods=total_periods,
                    max_page=max_page, page_index=page_index, missing=set(), has_data_map={})

    display_periods = periods

    # ---------- 依赖期扩展 ----------
    _all_formula_defs = _cached_formula_defs(con if con is not None else cur)
    _max_n_years = 0
    for it in group_items:
        if it.get("item_type") == "formula":
            _max_n_years = max(_max_n_years,
                _collect_formula_max_years_recursive(
                    it.get("formula") or "", _all_formula_defs))

    extra = set()
    for p in display_periods:
        try:
            p_int = int(p); year = p_int // 100
            _prev_q = _prev_quarter_period(p_int)
            extra.update([(year - 1) * 100 + 12, (year - 2) * 100 + 12,
                          p_int - 100, p_int - 200, _prev_q, _prev_q - 100])
            for n in range(1, _max_n_years + 1):
                extra.add(p_int - n * 100)
        except Exception:
            pass
    query_periods = list(dict.fromkeys(display_periods + list(extra)))

    # ---------- 涉及的底层表 ----------
    involved_fields, field_order = set(), []   # ← 改为 (t, f) 复合键
    _seen_keys = set()
    for it in group_items:
        if it.get("item_type") == "field":
            t = it.get("table_name") or sel_table
            f = it.get("field_name")
            if t and f:
                involved_fields.add((t, f))
                field_order.append(f"{t}.{f}")
        elif it.get("item_type") == "formula":
            fk = _safe_str(it.get("display_name")) or _safe_str(it.get("formula"))
            if fk and fk not in _seen_keys:
                _seen_keys.add(fk)
                field_order.append(fk)
            involved_fields |= _collect_formula_base_fields_recursive(
                it.get("formula") or "", _all_formula_defs)

    if not field_order:
        return dict(periods=[], pivot={}, field_order=[], audit_tip_map={},
                    period_links={}, items_meta={}, total_periods=total_periods,
                    max_page=max_page, page_index=page_index, missing=set(), has_data_map={})

    # —— 主查询：按 (table_name, field_name) 复合键精确过滤 ——
    stock_in = ",".join(["?"] * len(sel_comps))
    ph       = ",".join(["?"] * len(query_periods))
    _field_pairs_ph = ",".join(["(?,?)"] * len(involved_fields))
    _field_flat = [x for pair in sorted(involved_fields) for x in pair]

    if granularity == "latest":
        expr_filter, expr_params = "('')", []
    else:
        expr_filter = "(" + ",".join(["?"] * len(expr_types_needed)) + ")"
        expr_params = list(expr_types_needed)

    df_raw = pd.DataFrame()
    _COLS = ["stock_code", "table_name", "field_name",
             "report_period", "expr_type", "value", "value_raw"]
    if not involved_fields:
        df_raw = pd.DataFrame(columns=_COLS)
    else:
        try:
            df_raw = cur.execute(
                f"SELECT stock_code, table_name, field_name, report_period, "
                f"expr_type, value, value_raw FROM {TABLE} "
                f"WHERE stock_code IN ({stock_in}) AND granularity = ? AND owner_type = ? "
                f"AND report_period IN ({ph}) "
                f"AND expr_type IN {expr_filter} "
                f"AND (table_name, field_name) IN ({_field_pairs_ph})",
                list(sel_comps) + [granularity, owner_type]
                + query_periods + expr_params
                + _field_flat).df()
        except Exception as e:
            st.error(f"查询失败：{e}")
            df_raw = pd.DataFrame(columns=_COLS)

    # ---------- 审计意见 ----------
    audit_map, audit_tip_map = {}, {}
    try:
        adf = cur.execute(
            f"SELECT stock_code, report_period, field_name, value_raw FROM {TABLE} "
            f"WHERE stock_code IN ({stock_in}) AND granularity='record' AND table_name='fs_a' "
            f"AND field_name IN ('auditOpinionType','accountingFirm','accountant','auditRemark') "
            f"AND report_period IN ({ph})", list(sel_comps) + query_periods).df()
        tmp = {}
        for r in adf.itertuples(index=False):
            c = _safe_str(r.stock_code); p = int(r.report_period)
            tmp.setdefault(c, {}).setdefault(p, {})[r.field_name] = _safe_str(r.value_raw)
        for c, pd_ in tmp.items():
            for p, d in pd_.items():
                raw = d.get("auditOpinionType", "")
                audit_map.setdefault(c, {})[p] = AUDIT_OPINION_LABELS.get(raw, raw)
                firm, acc, remark = d.get("accountingFirm",""), d.get("accountant",""), d.get("auditRemark","")
                audit_tip_map.setdefault(c, {})[p] = " / ".join(x for x in (firm, acc, remark) if x)
    except Exception:
        pass

    # ---------- 构建 pivot ----------
    pivot = {}
    if audit_map:
        field_order.insert(0, "fs_a.auditOpinionType")
        pivot["fs_a.auditOpinionType"] = {}
        for c, pd_ in audit_map.items():
            pivot["fs_a.auditOpinionType"][c] = {}
            for p in periods:
                txt = pd_.get(p, "")
                pivot["fs_a.auditOpinionType"][c][p] = {"t": {"value": txt, "raw": txt}}

    for c, t, f, p, et, v, raw in zip(
        df_raw["stock_code"], df_raw["table_name"], df_raw["field_name"],
        df_raw["report_period"], df_raw["expr_type"],
        df_raw["value"], df_raw["value_raw"]):
        c, t, f = _safe_str(c), _safe_str(t), _safe_str(f)
        if not t or not f or not c: continue
        try: p = int(p)
        except Exception: continue
        et = _safe_str(et) or ("t" if granularity != "latest" else "")
        try:
            if v is None or pd.isna(v): v = raw
        except Exception: pass
        _pivot_set(pivot, f"{t}.{f}", c, p, et, {"value": v, "raw": raw})

    # 历史财报公式也允许引用 pm/hm 的最新快照。
    # 只加载当前公式/指标涉及的字段，并把快照值映射到本次查询的所有报告期。
    if granularity != "latest":
        latest_fields = sorted(
            (t, f) for t, f in involved_fields if t in ("pm", "hm")
        )
        if latest_fields:
            latest_pairs_ph = ",".join(["(?,?)"] * len(latest_fields))
            latest_field_flat = [x for pair in latest_fields for x in pair]
            latest_df = cur.execute(
                f"""
                WITH ranked AS (
                    SELECT stock_code, table_name, field_name, value, value_raw,
                           row_number() OVER (
                               PARTITION BY stock_code, table_name, field_name
                               ORDER BY report_period DESC
                           ) AS rn
                    FROM {TABLE}
                    WHERE granularity = 'latest'
                      AND stock_code IN ({stock_in})
                      AND (table_name, field_name) IN ({latest_pairs_ph})
                )
                SELECT stock_code, table_name, field_name, value, value_raw
                FROM ranked
                WHERE rn = 1
                """,
                list(sel_comps) + latest_field_flat,
            ).df()

            for c, t, f, v, raw in latest_df.itertuples(index=False, name=None):
                c, t, f = _safe_str(c), _safe_str(t), _safe_str(f)
                try:
                    if v is None or pd.isna(v):
                        v = raw
                except Exception:
                    pass

                key = f"{t}.{f}"
                for p in query_periods:
                    pdat = pivot.setdefault(key, {}).setdefault(c, {}).setdefault(p, {})
                    cell = {"value": v, "raw": raw}
                    # q4 在 t/c/ttm 语境下分别读取这些表达式类型。
                    # 仅填空位，避免覆盖数据库中已有的历史值。
                    for et in ("t", "c", "ttm"):
                        pdat.setdefault(et, cell)

    _show_set = set(show_types or [])
    _formula_needs_ttm = False
    for it in group_items:
        if it.get("item_type") == "formula":
            if re.search(r'\.\s*ttm\s*\]', it.get("formula") or ""):
                _formula_needs_ttm = True
                break
    _derived_needed = {k for k in
        ("t_y2y", "t_c2c", "c_y2y", "c_c2c", "c_2y", "ttm_y2y", "ttm_c2c")
        if k in _show_set}
    if ("ttm" in _show_set
        or "ttm_y2y" in _show_set
        or "ttm_c2c" in _show_set
        or _formula_needs_ttm):
        _derived_needed.add("ttm")
    _fill_missing_expr_types(pivot, query_periods, sel_comps, granularity, full_derived_periods=display_periods, needed_derived=_derived_needed)
    _formula_defs = _cached_formula_defs(con if con is not None else cur)

    # 已入库公式依赖递归展开，加入计算但不加入显示列表
    _formula_items_for_calc = list(group_items)

    _seen_formula_names = {
        it.get("display_name")
        for it in _formula_items_for_calc
        if it.get("item_type") == "formula" and it.get("display_name")
    }

    _pending_formula_items = [
        it for it in group_items
        if it.get("item_type") == "formula"
    ]

    while _pending_formula_items:
        it = _pending_formula_items.pop()
        for match in _FORMULA_REF_RE.finditer(it.get("formula") or ""):
            dep_name = match.group(1)
            if dep_name in _seen_formula_names:
                continue
            formula_expr = _formula_defs.get(dep_name)
            if not formula_expr:
                continue

            dep_item = {
                "item_type": "formula",
                "display_name": dep_name,
                "formula": formula_expr,
            }
            _formula_items_for_calc.append(dep_item)
            _seen_formula_names.add(dep_name)
            _pending_formula_items.append(dep_item)

    _missing = _apply_formula_items(pivot, _formula_items_for_calc, query_periods, sel_comps)
    _formula_keys = {(it.get("display_name") or it.get("formula"))
                     for it in group_items if it.get("item_type") == "formula"} - {None, ""}
    if _formula_keys:
        _fill_missing_expr_types(pivot, query_periods, sel_comps, granularity,
                                  only_keys=_formula_keys, _normalize=False, full_derived_periods=display_periods, needed_derived=_derived_needed)

    # ---------- 报告链接 ----------
    period_links = {}
    if len(sel_comps) == 1:
        try:
            ph2 = ",".join(["?"] * len(periods))
            ldf = cur.execute(
                f"SELECT report_period, field_name, value_raw FROM {TABLE} "
                f"WHERE stock_code=? AND granularity='record' AND table_name='fs_a' "
                f"AND field_name IN ('reportLink','reportDate') "
                f"AND report_period IN ({ph2})", [comp_head] + periods).df()
            tmp = {}
            for r in ldf.itertuples(index=False):
                tmp.setdefault(int(r.report_period), {})[r.field_name] = _safe_str(r.value_raw)
            for p, d in tmp.items():
                _raw_link = _safe_str(d.get("reportLink", ""))
                if _raw_link.startswith("{"):
                    _m = re.search(r"""['"]url['"]\s*:\s*['"]([^'"]+)['"]""", _raw_link)
                    _raw_link = _m.group(1) if _m else ""
                period_links[p] = {"link": _raw_link,
                                   "date": d.get("reportDate", "")}
        except Exception:
            pass

    # ---------- items_meta ----------
    items_meta = {}
    for it in group_items:
        if it.get("item_type") == "field":
            k = f"{it.get('table_name')}.{it.get('field_name')}"
        elif it.get("item_type") == "formula":
            k = it.get("display_name") or it.get("formula")
        else:
            continue
        if k: items_meta[k] = it

    has_data_map = _compute_has_data_map(pivot, field_order) if hide_empty else {}
    return dict(periods=periods, pivot=pivot, field_order=field_order,
                audit_tip_map=audit_tip_map, period_links=period_links,
                items_meta=items_meta, total_periods=total_periods,
                max_page=max_page, page_index=page_index, missing=_missing, has_data_map=has_data_map)

# ---------- Tab 1: 🎯 自定义财报透视（复刻理杏仁） ----------
def render_custom_report_tab(con):
    st.subheader("🎯 自定义财报透视")
    with st.container(border=True):
        st.markdown("##### 📋 数据选项")
    st.caption(
        "复刻理杏仁自定义财报界面：选择公司 → 时间范围 → 报表类型 → 粒度 → "
        "报表分组 → 累计/单季/同比/环比 → 高亮。支持导出 CSV。"
    )

    cur = con.cursor()
    all_companies = _cached_companies(con, TABLE)

    if not all_companies:
        st.warning("数据库暂无数据，请先运行采集脚本。")
        return

    cs1, cs2 = st.columns([1, 3])
    with cs1:
        sel_comps = st.multiselect("选择公司", all_companies,
                                   format_func=company_label,
                                   default=[all_companies[0]] if all_companies else [],
                                   key="cf_comps")
        with st.expander("选择对比公司", expanded=False):
            extra_comps = st.multiselect(
                "追加对比公司", [c for c in all_companies if c not in sel_comps],
                format_func=company_label, key="cf_compare_comps")
            if extra_comps:
                sel_comps = list(dict.fromkeys(sel_comps + extra_comps))
        with st.expander("选择同行业公司", expanded=False):
            if not sel_comps:
                st.info("请先选择主公司")
            else:
                _head = sel_comps[0]
                _industry = ""
                try:
                    _row = cur.execute(
                        f"SELECT industry FROM {COMPANY_TABLE} WHERE stock_code=?",
                        [_head],
                    ).fetchone()
                    if _row and _row[0]:
                        _industry = str(_row[0]).strip()
                except Exception:
                    _industry = ""

                if not _industry:
                    st.info("当前公司未采集行业信息（company.industry 为空）")
                else:
                    _level = st.radio(
                        "行业匹配范围",
                        ["同三级行业", "同一级行业"],
                        horizontal=True,
                        key=f"cf_peer_level_{_head}",
                    )
                    if _level == "同三级行业":
                        _peers = [
                            r[0] for r in cur.execute(
                                f"SELECT stock_code FROM {COMPANY_TABLE} "
                                f"WHERE industry=? AND stock_code<>? "
                                f"ORDER BY stock_code",
                                [_industry, _head],
                            ).fetchall()
                        ]
                    else:
                        _first = _industry.split("-")[0].strip()
                        if not _first:
                            st.info("行业字段格式异常，无法按一级行业匹配")
                            _peers = []
                        else:
                            _peers = [
                                r[0] for r in cur.execute(
                                    f"SELECT stock_code FROM {COMPANY_TABLE} "
                                    f"WHERE industry LIKE ? AND stock_code<>? "
                                    f"ORDER BY stock_code",
                                    [f"{_first}%", _head],
                                ).fetchall()
                            ]

                    _peer_sel = st.multiselect(
                        "追加同行业公司",
                        _peers,
                        format_func=company_label,
                        key=f"cf_peer_comps_{_head}",
                    )
                    if _peer_sel:
                        sel_comps = list(dict.fromkeys(sel_comps + _peer_sel))
        if not sel_comps:
            st.warning("请选择至少一家公司")
            return

    with cs2:
        def my_metric(col, label, val):
            with col:
                st.markdown(
                    f"<div style='font-size:14px; color:#666; margin-bottom:6px;'>{label}</div>"
                    f"<div style='font-size:26px; font-weight:400; color:#333; line-height:1.2; white-space:nowrap;'>{val}</div>",
                    unsafe_allow_html=True
                )
        
        # 概览以第一家公司为准
        comp_head = sel_comps[0]

        # ===== L1 快照（按 comp_head，只有换公司才重查）=====
        if st.session_state.get("cf_L1_key") != comp_head:
            lat_map = {}
            try:
                lat_df = cur.execute(
                    f"SELECT table_name, field_name, value, value_raw FROM {TABLE} "
                    f"WHERE stock_code = ? AND granularity = 'latest'", [comp_head]).df()
                for _, r in lat_df.iterrows():
                    v = r.get("value")
                    try:
                        if v is None or pd.isna(v): v = r.get("value_raw")
                    except Exception: pass
                    lat_map[f"{r['table_name']}.{r['field_name']}"] = v
            except Exception:
                pass

            industry_txt = province_txt = ""
            company_type_db = "non_financial"
            try:
                row = cur.execute(
                    f"SELECT industry, province, company_type FROM {COMPANY_TABLE} "
                    f"WHERE stock_code = ?", [comp_head]).fetchone()
                if row:
                    industry_txt = str(row[0] or "").strip()
                    province_txt = str(row[1] or "").strip()
                    company_type_db = str(row[2] or "non_financial").strip()
            except Exception:
                try:
                    row = cur.execute(
                        f"SELECT industry, company_type FROM {COMPANY_TABLE} "
                        f"WHERE stock_code = ?", [comp_head]).fetchone()
                    if row:
                        industry_txt = str(row[0] or "").strip()
                        company_type_db = str(row[1] or "non_financial").strip()
                except Exception:
                    pass

            try:
                pb_row = cur.execute(
                    f"SELECT min(report_period), max(report_period) FROM {TABLE} "
                    f"WHERE stock_code = ? AND granularity <> 'latest'",
                    [comp_head]).fetchone()
                pb_min, pb_max = int(pb_row[0] or 0), int(pb_row[1] or 0)
            except Exception:
                pb_min, pb_max = 0, 0

            st.session_state["cf_L1_key"]  = comp_head
            st.session_state["cf_L1_lat"]  = lat_map
            st.session_state["cf_L1_meta"] = (industry_txt, province_txt, company_type_db)
            st.session_state["cf_L1_pb"]   = (pb_min, pb_max)

        lat_map = st.session_state["cf_L1_lat"]
        ipo_date = _to_cn_date(_safe_str(lat_map.get("pm.ipoDate")))
        industry_txt, province_txt, sel_company_type = st.session_state["cf_L1_meta"]
        name = COMPANY_NAME_MAP.get(_safe_str(comp_head), comp_head)
        if len(sel_comps) > 1:
            name += f" 等 {len(sel_comps)} 家公司"
        
        badges = []
        if lat_map.get("hm.mm_ha.mm_sh"):
            badges.append("沪股通" if str(comp_head).startswith("6") else "深股通")
        if lat_map.get("hm.mtasl.mtaslb"):
            badges.append("融资融券")
        if lat_map.get("hm.ple.ps"):
            badges.append("股权质押")
        _dz_date = _to_cn_date(_safe_str(lat_map.get("hm.t_a.last_data_date")))
        if _dz_date:
            badges.append(f"最新大宗交易 ({_dz_date})")
        badge_html = " ".join(
            f'<span style="background:#0d6efd;color:#fff;padding:1px 5px;'
            f'border-radius:3px;font-size:11px;margin-left:4px">{b}</span>'
            for b in badges)

        # 标题行加代码后缀
        mkt_suffix = {"6": "sh", "9": "sh", "0": "sz", "2": "sz", "3": "sz", "4": "bj", "8": "bj"}.get(str(comp_head)[:1], "sh")
        region = province_txt
        st.markdown(
            f"### {name} {badge_html} "
            f"<span style='color:#666;font-size:0.55em'>"
            f"({region} {comp_head}.{mkt_suffix})</span>",
            unsafe_allow_html=True)

        # 申万三级行业徽章
        if industry_txt:
            parts = [p for p in industry_txt.split("-") if p]
            badges_html = " ".join(
                f"<span style='background:#198754;color:#fff;padding:1px 6px;"
                f"border-radius:3px;font-size:11px'>{_html_mod.escape(p)}</span>"
                for p in parts)
            st.markdown(
                f"申万: {badges_html}",
                unsafe_allow_html=True)

        def _num(v, nd=2):
            try: return f"{float(v):,.{nd}f}" if v not in (None, "") else ""
            except Exception: return ""
        def _yi(v):
            try: return f"{float(v)/1e8:,.2f}亿元" if v not in (None, "") else ""
            except Exception: return ""
        def _wan(v):
            try: return f"{float(v)/1e4:,.2f}万" if v not in (None, "") else ""
            except Exception: return ""
        def _pct(v):
            try: return f"{float(v)*100:.2f}%" if v not in (None, "") else ""
            except Exception: return ""
        def _shares(mc_key, sp_key):
            mc, sp = lat_map.get(mc_key), lat_map.get(sp_key)
            try:
                return f"{float(mc)/float(sp)/1e8:,.2f}亿"
            except Exception:
                return ""
        def _ratio_detail(main_r, *parts):
            """parts: (label, value_str) 交错传入；value_str 空则跳过"""
            if main_r in (None, ""): return ""
            s = _pct(main_r)
            chunks = []
            for i in range(0, len(parts), 2):
                lab, val = parts[i], parts[i+1]
                if val:
                    chunks.append(f"{lab} {val}".strip())
            if chunks:
                s += (f" <span style='color:#999;font-size:0.7em'>"
                      f"({' · '.join(chunks)})</span>")
            return s

        # 1. 核心估值指标 (一行 3 列)
        row1 = st.columns(3)
        my_metric(row1[0], "PE-TTM", _num(lat_map.get("pm.pe_ttm")))
        my_metric(row1[1], "PB", _num(lat_map.get("pm.pb")))
        my_metric(row1[2], "股息率", _pct(lat_map.get("pm.dyr")))

        # 2. fluid-metrics 横排紧凑指标 (完美复刻 HTML)
        fluid_items = [
            ("上市时间", ipo_date),
            ("股价", _num(lat_map.get("pm.sp")) + "元" if _num(lat_map.get("pm.sp")) else ""),
            ("涨跌幅", _pct(lat_map.get("pm.spc"))),
            ("成交金额", _yi(lat_map.get("pm.ta"))),
            ("换手率", _pct(lat_map.get("pm.to_r"))),
            ("总市值", _yi(lat_map.get("pm.mc"))),
            ("A股市值", _yi(lat_map.get("pm.mc_om"))),
            ("流通市值", _yi(lat_map.get("pm.cmc"))),
            ("自由流通市值", _yi(lat_map.get("pm.ecmc"))),
            ("总股东人数", _wan(lat_map.get("pm.shn"))),
            ("人均自由流通市值", _wan(lat_map.get("pm.ecmc_psh")) + "元" if _wan(lat_map.get("pm.ecmc_psh")) else ""),
            ("总股本", _shares("pm.mc", "pm.sp")),
            ("流通A股", _shares("pm.cmc", "pm.sp")),
            ("陆股通持股占流通A股比例",
             _ratio_detail(lat_map.get("hm.mm_ha.mm_sh_cap_r"),
                           "",  _yi(lat_map.get("hm.mm_ha.mm_sha")),
                           "",  _to_cn_date(_safe_str(lat_map.get("hm.mm_ha.last_data_date"))))),
            ("融资融券余额占流通A股市值比例",
             _ratio_detail(lat_map.get("hm.mtasl.mtaslb_mc_r"),
                           "融资", _yi(lat_map.get("hm.mtasl.mtaslb_fb")),
                           "融券", _yi(lat_map.get("hm.mtasl.mtaslb_sb")),
                           "",    _to_cn_date(_safe_str(lat_map.get("hm.mtasl.last_data_date"))))),
            ("质押股数与前十大股东持股之比",
             _ratio_detail(lat_map.get("hm.ple.ps_shbt10sh_r"),
                           "",  _yi(lat_map.get("hm.ple.ps_mc")),
                           "",  _to_cn_date(_safe_str(lat_map.get("hm.ple.last_data_date"))))),
            ("上市至今年化投资收益率", _pct(lat_map.get("hm.tr_dri.cagr_p_r_fs"))),
            ("实际控制人", _safe_str(lat_map.get("hm.o.a_c")) or "无"),
        ]

        fluid_html = ""
        for k, v in fluid_items:
            if not v:
                v = "--"
            fluid_html += (f"<span style='font-size:13px; margin-right:24px; line-height:2; white-space:nowrap;'>"
                           f"<span style='color:#666;'>{k}</span> "
                           f"<span style='color:#0d6efd; font-weight:500;'>{v}</span></span>")
        
        st.markdown(f"<div style='display:flex; flex-wrap:wrap; margin-top:15px;'>{fluid_html}</div>", unsafe_allow_html=True)

    st.divider()

    st.markdown("##### 🔧 数据选项")
    from datetime import date, timedelta

    if "cf_start_date" not in st.session_state:
        st.session_state.cf_start_date = date.today() - timedelta(days=365 * 200)
    if "cf_end_date" not in st.session_state:
        st.session_state.cf_end_date = date.today()

    # ---- 快捷日期选择：放 form 外（联动）----
    qc = st.columns([1, 1, 1, 1, 1, 1, 3])
    for i, years in enumerate([30, 20, 10, 5, 3, 2]):
        with qc[i]:
            if st.button(f"{years}年", key=f"cf_q_{years}", width='stretch'):
                st.session_state.cf_end_date = date.today()
                st.session_state.cf_start_date = date.today() - timedelta(days=365 * years)
                st.rerun()

    # ---- 数据参数控件（form 内 / 外）----
    def _render_data_controls():
        tc1, tc2 = st.columns([1, 1])
        with tc1: sd = st.date_input("起始时间", key="cf_start_date")
        with tc2: ed = st.date_input("结束时间", key="cf_end_date")
        rc1, rc2 = st.columns([1, 1])
        with rc1:
            ol = st.segmented_control("报表类型", ["合并报表", "母公司报表"],
                                      default="合并报表", key="cf_owner")
        with rc2:
            gl = st.segmented_control("粒度", ["季度", "半年", "年度", "最新"],
                                      default="季度", key="cf_gran")
        return sd, ed, ol, gl

    submit_mode = st.radio("提交方式", ["自动提交", "手动提交"],
                           horizontal=True, key="cf_submit_mode")

    if submit_mode == "手动提交":
        with st.form("cf_data_form", border=False):
            sd, ed, ol, gl = _render_data_controls()
            submitted = st.form_submit_button("🔍 应用筛选", type="primary")
        if submitted:
            st.session_state["cf_data_eff"] = dict(
                sel_comps=list(sel_comps),
                start_date=sd, end_date=ed, owner_label=ol, gran_label=gl)
        eff = st.session_state.get("cf_data_eff")
        if not eff:
            st.info("调整数据参数后请点击【应用筛选】"); return
        if eff["sel_comps"] != list(sel_comps):
            st.warning("公司已变化，请点击【应用筛选】重新提交。"); return
        sd, ed, ol, gl = eff["start_date"], eff["end_date"], eff["owner_label"], eff["gran_label"]
    else:
        st.session_state.pop("cf_data_eff", None)
        sd, ed, ol, gl = _render_data_controls()

    if sd > ed:
        st.error("起始时间必须小于结束时间"); return
    start_period = int(sd.strftime("%Y%m"))
    end_period   = int(ed.strftime("%Y%m"))
    owner_type   = "consolidated" if ol == "合并报表" else "parent_company"
    granularity  = {"季度": "q", "半年": "hy", "年度": "y", "最新": "latest"}[gl]
    sel_table    = "bs"

    _gk = (owner_type, sel_company_type)
    if st.session_state.get("cf_groups_key") != _gk:
        groups = _ensure_default_group(cur, owner_type=owner_type,
                                       company_type=sel_company_type)
        st.session_state["cf_groups_key"] = _gk
        st.session_state["cf_groups"]     = groups
    groups = st.session_state["cf_groups"]
    if not groups:
        st.warning(f"该公司在 {gl} / {ol} 下暂无数据"); return

    gc1, gc2, gc3, gc4, gc5, gc6 = st.columns([3, 1, 1, 1, 1, 1.2])
    with gc1:
        group_map = {g["group_id"]: g["group_name"] for g in groups}
        sel_group_id = st.radio(
            "分组",
            list(group_map.keys()),
            format_func=lambda gid: group_map.get(gid, gid),
            horizontal=True,
            key="cf_group_id_radio",
        )
        sel_group = next(g for g in groups if g["group_id"] == sel_group_id)
        sel_group_name = group_map.get(sel_group_id, sel_group_id)
        group_id = sel_group["group_id"]
        st.session_state["cf_group_id"] = group_id
    with gc2:
        if st.button("新建分组", key="cf_create_group_btn"): st.session_state["cf_show_create_group"] = True
    with gc3:
        if st.button("删除分组", key="cf_del_group_btn"): st.session_state["cf_show_del_group"] = True
    with gc4:
        if st.button("批量删除分组", key="cf_batch_del_btn", width='stretch'): st.session_state["cf_show_batch_del"] = True
    with gc5:
        if st.button("重命名", key="cf_rename_btn"): st.session_state["cf_show_rename"] = True
    with gc6:
        if st.button("数据显示设置", key="cf_metric_btn"): st.session_state["cf_show_metric_dialog"] = True

    # ---------- 分组上移 / 下移（拖拽替代） ----------
    _group_ids = [g["group_id"] for g in groups]
    _idx_sel = _group_ids.index(sel_group_id)
    _uc1, _uc2, _ = st.columns([1, 1, 6])
    with _uc1:
        if st.button("⬆️ 分组上移", key="cf_group_up",
                     disabled=(_idx_sel == 0), width='stretch'):
            groups[_idx_sel - 1], groups[_idx_sel] = (
                groups[_idx_sel], groups[_idx_sel - 1])
            _persist_group_order(cur, groups)
            _invalidate_groups_cache()
            st.rerun()
    with _uc2:
        if st.button("⬇️ 分组下移", key="cf_group_down",
                     disabled=(_idx_sel >= len(groups) - 1), width='stretch'):
            groups[_idx_sel], groups[_idx_sel + 1] = (
                groups[_idx_sel + 1], groups[_idx_sel])
            _persist_group_order(cur, groups)
            _invalidate_groups_cache()
            st.rerun()

    if st.session_state.get("cf_show_create_group"):
        _create_group_dialog(con, sel_table, owner_type, sel_company_type)
    if st.session_state.get("cf_show_del_group"):
        _delete_group_dialog(con, group_id, sel_group_name)
    if st.session_state.get("cf_show_batch_del"):
        _batch_delete_groups_dialog(con, groups)

    st.markdown("##### ⚙️ 显示设置")
    sc1, sc2, sc3, sc4 = st.columns([1.5, 1, 1, 1])
    with sc1:
        if granularity != "latest":
            show_types = st.multiselect("显示类型", options=["t", "t_r", "c", "c_r", "ttm", "c_2y", "t_y2y", "t_c2c", "ttm_y2y", "ttm_c2c", "c_y2y", "c_c2c"],
                default=["t", "c", "t_y2y", "t_c2c", "c_y2y", "c_c2c"],
                format_func=lambda x: EXPR_TYPE_LABELS.get(x, x), key="cf_show_types")
        else:
            show_types = []
    with sc2:
        page_size = st.number_input("每页季度数", min_value=1, max_value=30, value=9, step=1, key="cf_psize")
    with sc3:
        view_mode = st.radio("显示", ["所有数据", "隐藏无数据指标"], horizontal=True, key="cf_view_mode")
        hide_empty = (view_mode == "隐藏无数据指标")
    with sc4:
        report_type = st.selectbox("报表类型", ["全部", "一季报", "中报", "三季报", "年报"], key="cf_report_type")

    # 高亮（唯一一处 number_input，用 input-group 样式近似）
    hc1, hc2 = st.columns([1, 1])
    with hc1:
        st.markdown("<div style='font-size:12px;color:#666;margin-bottom:2px'>增加 ≥ %</div>",
                    unsafe_allow_html=True)
        hl_up = st.number_input("增加 ≥ %", value=50, step=10,
                                key="cf_hlup", label_visibility="collapsed")
    with hc2:
        st.markdown("<div style='font-size:12px;color:#666;margin-bottom:2px'>减少 ≤ %</div>",
                    unsafe_allow_html=True)
        hl_down = st.number_input("减少 ≤ %", value=-50, step=10,
                                  key="cf_hldown", label_visibility="collapsed")

    if st.session_state.get("cf_show_metric_dialog"):
        _metric_settings_dialog(con, group_id, sel_table, granularity, owner_type, sel_company_type)
    if st.session_state.get("cf_show_rename"):
        _rename_group_dialog(con, group_id, sel_group_name)

    _state_key = (f"{comp_head}_{granularity}_{ol}_{report_type}_{group_id}_"
                  f"{start_period}_{end_period}")
    if st.session_state.get("cf_last_state_key") != _state_key:
        st.session_state["cf_page_index"] = 0
        st.session_state["cf_last_state_key"] = _state_key

    _group_items = _cached_group_items(con, group_id)
    expr_types_needed = {"t", "c"}
    if "t_r" in show_types: expr_types_needed.add("t_r")
    if "c_r" in show_types: expr_types_needed.add("c_r")
    if ("ttm" in show_types
        or any(re.search(r'\.\s*ttm\s*\]', _safe_str(it.get("formula")))
               for it in _group_items)):
        expr_types_needed.add("ttm")
    # ⚠️ t_y2y/t_c2c/c_y2y/c_c2c/c_2y/ttm_y2y/ttm_c2c 全部不进 SQL
    #    因为它们由 _fill_missing_expr_types 补算；加进来只会让 SQL 反复 miss

    if "cf_page_index" not in st.session_state:
        st.session_state["cf_page_index"] = 0
    page_index = st.session_state["cf_page_index"] if granularity != "latest" else -1

    _L2_key = (
        tuple(sel_comps),
        granularity, owner_type,
        start_period, end_period,
        group_id, report_type,
        page_index,
        int(page_size),
        tuple(sorted(expr_types_needed)), bool(hide_empty),
    )

    if st.session_state.get("cf_L2_key") != _L2_key:
        with st.spinner("查询透视数据…"):
            L2 = _cf_build_L2(
                cur=cur, sel_comps=sel_comps, comp_head=comp_head,
                granularity=granularity, owner_type=owner_type,
                start_period=start_period, end_period=end_period,
                group_id=group_id, report_type=report_type,
                page_index=page_index, page_size=int(page_size),
                expr_types_needed=expr_types_needed,
                group_items=_group_items, sel_table=sel_table,
                sel_company_type=sel_company_type, con=con, hide_empty=bool(hide_empty), show_types=show_types)
        st.session_state["cf_L2_key"]    = _L2_key
        st.session_state["cf_L2"]        = L2
        st.session_state["cf_page_index"] = L2["page_index"]

    L2 = st.session_state["cf_L2"]
    periods       = L2["periods"]
    pivot         = L2["pivot"]
    field_order   = L2["field_order"]
    audit_tip_map = L2["audit_tip_map"]
    period_links  = L2["period_links"]
    items_meta    = L2["items_meta"]
    total_periods = L2["total_periods"]
    max_page      = L2["max_page"]
    page_index    = L2["page_index"]

    if not periods:
        st.info("当前条件下无数据，请调整时间范围或切换报表。"); return

    if L2.get("missing"):
        st.warning(
            f"⚠️ 以下被引用的公式不存在，对应单元格显示为 `--`："
            f"{'、'.join(sorted(L2['missing']))}"
        )

    st.caption(
        f"共 **{len(field_order)}** 个指标，"
        f"展示 **{len(periods)}** 个报告期 "
        f"（{len(sel_comps)} 家公司 · {gl} · {ol}）"
    )

    _render_key = (
        _L2_key,
        tuple(sorted(show_types or [])),
        float(hl_up) if hl_up else 0,
        float(hl_down) if hl_down else 0,
        bool(hide_empty),
    )

    _cur_metric_map = METRIC_MAPS.get(sel_company_type, METRIC_MAPS["__all__"])
    with st.spinner("渲染透视表…"):
        _render_custom_table(
            pivot, periods, field_order, show_types,
            float(hl_up) if hl_up else 0,
            float(hl_down) if hl_down else 0,
            sel_table, companies=sel_comps,
            company_name=COMPANY_NAME_MAP.get(_safe_str(comp_head), ""),
            items_meta=items_meta, audit_tips=audit_tip_map,
            is_latest=(granularity == "latest"), period_links=period_links,
            metric_map=_cur_metric_map,
            hide_empty=bool(hide_empty),
            cache_key=_render_key,
            has_data_map=L2.get("has_data_map"),
        )

    if granularity != "latest":
        c1, c2, c3 = st.columns([1, 1, 4])
        with c1:
            if st.button("← 上一页", disabled=page_index <= 0, key="cf_prev"):
                st.session_state["cf_page_index"] -= 1
                st.rerun()
        with c2:
            if st.button("下一页 →", disabled=page_index >= max_page, key="cf_next"):
                st.session_state["cf_page_index"] += 1
                st.rerun()
        with c3:
            st.caption(f"**{len(periods)}个季度** 共 {total_periods} 个报告期 （第 {page_index+1}/{max_page+1} 页）")

    if st.button("📥 准备导出 CSV", key="cf_prep_export"):
        _rows = []
        _cur_metric_map = METRIC_MAPS.get(sel_company_type, METRIC_MAPS["__all__"])
        for fn in field_order:
            tab_name, real_fn = fn.split(".", 1) if "." in fn else (sel_table, fn)
            name_cn = _cur_metric_map.get((tab_name, real_fn), "") or real_fn
            for comp in sel_comps:
                comp_fdata = pivot.get(fn, {}).get(comp, {})
                if not comp_fdata: continue
                row = {"指标": name_cn,
                       "公司": COMPANY_NAME_MAP.get(_safe_str(comp), comp),
                       "字段名": fn}
                for p in periods:
                    yr, q = _split_period(p)
                    pdat = comp_fdata.get(p, {})
                    if granularity == "latest":
                        k = "t" if "t" in pdat else ""
                        row[f"{yr}{q}_原值"] = _cell_val(pdat.get(k))
                    else:
                        for ek, cd in pdat.items():
                            cn = EXPR_TYPE_LABELS.get(ek, ek) or "原值"
                            if cn == "（无）": cn = "原值"
                            row[f"{yr}{q}_{cn}"] = _cell_val(cd)
                _rows.append(row)
        st.session_state["cf_export_bytes"] = (
            pd.DataFrame(_rows).to_csv(index=False).encode("utf-8-sig")
            if _rows else b"")
        st.session_state["cf_export_key"] = _L2_key

    if (st.session_state.get("cf_export_bytes")
            and st.session_state.get("cf_export_key") == _L2_key):
        st.download_button(
            "⬇️ 下载 CSV",
            data=st.session_state["cf_export_bytes"],
            file_name=f"{len(sel_comps)}家_{sel_table}_{granularity}_"
                      f"{datetime.now():%Y%m%d_%H%M%S}.csv",
            mime="text/csv", width='stretch')

    if st.button("🖼️ 准备导出图片", key="cf_prep_img"):
        st.session_state["cf_export_png_ready"] = True

    if st.session_state.get("cf_export_png_ready"):
        _html = st.session_state.get("_cf_last_html")
        if not _html:
            st.info("请先渲染表格")
        else:
            try:
                from html2image import Html2Image
                _hti = Html2Image(size=(1920, 1080), browser='edge', output_path=".")
                _png = _hti.screenshot(
                    html_str=_html,
                    save_as=f"cf_{datetime.now():%Y%m%d_%H%M%S}.png"
                )[0]
                with open(_png, "rb") as _f:
                    st.download_button(
                        "⬇️ 下载 PNG", _f.read(),
                        file_name=Path(_png).name, mime="image/png",
                        key="cf_dl_png")
                Path(_png).unlink(missing_ok=True)   # 下载后清理临时文件
            except ImportError:
                st.warning("未安装 html2image。请运行：pip install html2image（需本机 Chrome）")
            except Exception as _e:
                st.error(f"导出图片失败：{_e}")

if active_tab == _TAB_LABELS[1]:
    render_custom_report_tab(con)

# ---------- Tab 2: 编辑与新增 ----------
if active_tab == _TAB_LABELS[2]:
    st.subheader("✏️ 内联编辑 & 新增行")
    st.caption("修改单元格后点击【保存全部修改】；表格底部可新增行；"
               "勾选行后按 Delete 键删除行。中文名列只读。")
    with st.expander(f"🔎 编辑范围筛选（一次最多加载 {MAX_EDIT_ROWS} 行）",
                     expanded=True):
        ef = filter_panel("edit")
    ewhere, eparams = build_where(**ef)

    if st.button("📥 加载待编辑数据", type="primary"):
        try:
            df_e = load_df(ewhere, eparams, limit=MAX_EDIT_ROWS)
            st.session_state["edit_original"] = df_e.copy()
            st.success(f"已加载 {len(df_e)} 行")
        except Exception as e:
            st.error(f"加载失败：{e}")

    if "edit_original" in st.session_state \
            and not st.session_state["edit_original"].empty:
        original = st.session_state["edit_original"]
        col_cfg = build_column_config(original.columns)
        edited = st.data_editor(
            original, key="edit_editor", num_rows="dynamic",
            width='stretch', hide_index=True, column_config=col_cfg)

        c1, c2, _ = st.columns([1, 1, 2])
        with c1:
            save_clicked = st.button("💾 保存全部修改", type="primary",
                                     width='stretch')
        with c2:
            if st.button("↩️ 撤销未保存修改", width='stretch'):
                del st.session_state["edit_original"]
                st.rerun()

        if save_clicked:
            try:
                n_del, n_wr = save_edits(con, original, edited)
                st.success(f"✅ 已保存：删除 {n_del} 行，写入 {n_wr} 行")
                scalar_cached.clear()
                del st.session_state["edit_original"]
                st.rerun()
            except Exception as e:
                st.error(f"保存失败：{e}")


# ---------- Tab 3: 批量操作 ----------
if active_tab == _TAB_LABELS[3]:
    st.subheader("🗑️ 批量操作")
    st.warning("以下操作不可撤销，请谨慎使用。")
    with st.expander("🔎 选择要操作的数据范围", expanded=True):
        bf = filter_panel("batch")
    bwhere, bparams = build_where(**bf)
    matched = scalar(f"SELECT count(*) FROM {TABLE}{bwhere}", bparams) or 0
    st.info(f"当前筛选命中 **{matched:,}** 行")

    col_a, _ = st.columns(2)
    with col_a:
        st.markdown("#### 🗑️ 按筛选条件删除")
        confirm_del = st.checkbox("我确认要删除以上筛选命中的全部数据")
        if st.button("执行删除", type="primary",
                     disabled=not confirm_del, width='stretch'):
            try:
                cur = con.cursor()
                cur.execute(f"DELETE FROM {TABLE}{bwhere}", bparams)
                st.success(f"已删除 {matched:,} 行")
                scalar_cached.clear()
                st.rerun()
            except Exception as e:
                st.error(f"删除失败：{e}")


# ---------- Tab 5: 数据质量 ----------
if active_tab == _TAB_LABELS[4]:
    st.subheader("📈 数据质量概览")
    c1, c2 = st.columns(2)
    with c1:
        st.markdown("#### 表名 × 粒度 分布")
        df_rep    = _dq_table_granularity(con)
        if not df_rep.empty:
            df_rep["table_cn"] = df_rep["table_name"].map(
                lambda x: _label(REPORT_TYPE_LABELS, x))
            df_rep["granularity_cn"] = df_rep["granularity"].map(
                lambda x: _label(GRANULARITY_LABELS, x))
        st.dataframe(df_rep, width='stretch', hide_index=True)
    with c2:
        st.markdown("#### 报告期分布（最近 20 期，不含 latest）")
        df_period = _dq_period_dist(con)
        st.dataframe(df_period, width='stretch', hide_index=True)

    st.markdown("#### 表达式类型分布")
    df_expr   = _dq_expr_dist(con)
    if not df_expr.empty:
        df_expr["expr_cn"] = df_expr["expr_type"].map(
            lambda x: _label(EXPR_TYPE_LABELS, x))
    st.dataframe(df_expr, width='stretch', hide_index=True)

    st.markdown("#### latest 快照（hm/pm）概览")
    try:
        df_lat    = _dq_latest_top(con)
        if df_lat.empty:
            st.info("暂无 latest 快照数据（可能尚未运行采集脚本-最新数据.py）。")
        else:
            st.dataframe(df_lat, width='stretch', hide_index=True)
    except Exception as e:
        st.warning(f"检查失败：{e}")

    st.markdown("#### 未匹配到中文名的字段（Top 50）")
    try:
        all_fields = _dq_all_fields(con)
        miss = []
        for _, r in all_fields.iterrows():
            k = (str(r["table_name"]), str(r["field_name"]))
            if k not in METRIC_MAP or not METRIC_MAP[k]:
                miss.append({"table_name": k[0], "field_name": k[1]})
        if miss:
            st.dataframe(pd.DataFrame(miss).head(50),
                         width='stretch', hide_index=True)
        else:
            st.success("✅ 所有字段均已匹配中文名")
    except Exception as e:
        st.warning(f"检查失败：{e}")


# ---------- Tab 6: 数据采集 ----------
if active_tab == _TAB_LABELS[5]:
    st.subheader("⚡ 重新采集 / 增量补采")
    st.info(
        "为保证并发与请求节流安全，采集功能需在命令行执行：\n\n"
        "- **行情/公司概况快照**：`python 采集脚本-最新数据.py`\n"
        "  → 写 `granularity='latest'`，`report_period=YYYYMMDD`\n"
        "- **财报历史数据**：`python 采集脚本-财报数据.py`\n"
        "  → 写 `granularity IN ('y','hy','q','record')`，"
        "`report_period=YYYYMM`\n\n"
        "采集完成后回到本页点击【🔄 清空缓存并重新连接】即可看到新数据。"
    )
    st.markdown("##### 快速核对采集结果")
    if st.button("🔍 检查 fs_data 与 metric_dict"):
        try:
            n_fs = scalar_cached(f"SELECT count(*) FROM {TABLE}") or 0
            n_md = scalar_cached(f"SELECT count(*) FROM {METRIC_TABLE}") or 0
            n_comp = scalar_cached(f"SELECT count(DISTINCT stock_code) FROM {TABLE}") or 0
            n_lat = scalar_cached(f"SELECT count(*) FROM {TABLE} WHERE granularity='latest'") or 0
            n_fin = scalar_cached(f"SELECT count(*) FROM {TABLE} WHERE granularity<>'latest'") or 0
            st.write(f"- fs_data 总行数：**{n_fs:,}**")
            st.write(f"  - latest 快照：**{n_lat:,}** 行")
            st.write(f"  - 财报历史：**{n_fin:,}** 行")
            st.write(f"- metric_dict 指标数：**{n_md:,}**")
            st.write(f"- 已采集公司数：**{n_comp:,}**")
            st.write(f"- 本页加载的中文映射：**{len(METRIC_MAP):,}**")
        except Exception as e:
            st.error(f"检查失败：{e}")


# ---------- Tab 7: SQL 控制台 ----------
if active_tab == _TAB_LABELS[6]:
    st.subheader("🛠️ SQL 控制台与表结构")

    col_s1, col_s2, col_s3, col_s4 = st.columns(4)
    if col_s1.button("📋 查看 fs_data 结构"):
        st.session_state["sql_text"] = f"DESCRIBE {TABLE};"
    if col_s2.button("🔍 查看当前行数"):
        st.session_state["sql_text"] = f"SELECT count(*) AS 总行数 FROM {TABLE};"
    if col_s3.button("📊 各表数据量"):
        st.session_state["sql_text"] = (
            f"SELECT table_name, granularity, count(*) AS rows "
            f"FROM {TABLE} GROUP BY 1, 2 ORDER BY 3 DESC;")
    if col_s4.button("📚 查看指标字典"):
        st.session_state["sql_text"] = f"SELECT * FROM {METRIC_TABLE} LIMIT 100;"

    default_sql = ""
    if "sql_text" not in st.session_state:
        st.session_state["sql_text"] = default_sql

    sql = st.text_area("SQL 语句", height=180, key="sql_text")
    run_sql = st.button("▶️ 执行", type="primary")

    if run_sql and sql.strip():
        try:
            start = time.time()
            cur = con.cursor()
            cur.execute(f"USE {ALIAS};")
            
            # 改用最原始的方式取数据，彻底避开 .df() 的类型推断 Bug
            cur.execute(sql)
            rows = cur.fetchall()
            cols = [d[0] for d in cur.description] if cur.description else []
            
            elapsed = time.time() - start
            if not rows:
                st.success(f"✅ 执行成功（无返回行） · {elapsed*1000:.0f} ms")
            else:
                st.success(f"✅ 返回 {len(rows):,} 行 · {elapsed*1000:.0f} ms")
                result_df = pd.DataFrame(rows, columns=cols)
                # 仅对 object 列（Decimal/date/混合类型）转 str；数值列原样交给 st.dataframe
                for _c in result_df.columns:
                    _s = result_df[_c]
                    if _s.dtype == object:
                        result_df[_c] = _s.astype(str).where(_s.notna(), None)
                st.dataframe(result_df, width='stretch', hide_index=True)
        except Exception as e:
            st.error(f"❌ 执行失败：{e}")


# ---------- Tab 8: 表结构管理（全表版） ----------
if active_tab == _TAB_LABELS[7]:
    st.subheader("⚙️ 表结构管理")

    _ALL_TABLES = ["fs_data", "metric_dict", "company",
                   "custom_metric_group", "custom_metric_group_item",
                   "dim_constants"]

    tgt = st.selectbox("目标表", _ALL_TABLES, key="ddl_target_table")
    FQTN = f"{ALIAS}.main.{tgt}"

    _t1, _t2, _t3, _t4, _t5, _t6 = st.tabs(
        ["📋 结构与元数据", "🧱 列操作", "📇 索引/视图", "📤 DDL 导出",
         "🗂️ DuckLake 元数据", "☢️ 危险区"])

    # ---------- 1. 结构与元数据 ----------
    with _t1:
        try:
            schema_df = con.cursor().execute(f"DESCRIBE {FQTN}").df()
            row_n = scalar(f"SELECT count(*) FROM {FQTN}") or 0
            st.caption(f"表 `{tgt}` · 共 **{len(schema_df)}** 列 · **{row_n:,}** 行")
            st.dataframe(schema_df, width='stretch', hide_index=True)
            current_columns = schema_df["column_name"].tolist()
        except Exception as e:
            st.error(f"读表结构失败：{e}")
            current_columns = []

        try:
            idx_df = con.cursor().execute(
                f"SELECT index_name, is_unique, is_primary, expressions "
                f"FROM duckdb_indexes() WHERE schema_name='main' "
                f"AND table_name='{tgt}'").df()
            st.markdown("**索引**")
            st.dataframe(idx_df, width='stretch', hide_index=True)
        except Exception:
            pass

        try:
            vw_df = con.cursor().execute(
                f"SELECT table_name AS view_name FROM information_schema.views "
                f"WHERE table_schema='main'").df()
            st.markdown("**视图**")
            st.dataframe(vw_df, width='stretch', hide_index=True)
        except Exception:
            pass

    # ---------- 2. 列操作 ----------
    with _t2:
        st.markdown("##### ➕ 新增列")
        c1, c2, c3 = st.columns([2, 2, 2])
        with c1: _new = st.text_input("列名", key="ddl_add_name")
        with c2: _typ = st.selectbox("类型",
            ["VARCHAR","INTEGER","BIGINT","DOUBLE","BOOLEAN","TIMESTAMP","DATE"],
            key="ddl_add_type")
        with c3: _dft = st.text_input("DEFAULT（可空）", key="ddl_add_default")
        if st.button("确认新增", type="primary", key="ddl_add_btn"):
            try:
                _sql = f"ALTER TABLE {FQTN} ADD COLUMN {_new} {_typ}"
                if _dft.strip():
                    _sql += f" DEFAULT {_dft.strip()}"
                con.cursor().execute(_sql)
                st.success(f"✅ 新增列 {_new} ({_typ})")
                st.rerun()
            except Exception as e:
                st.error(f"❌ {e}")

        st.divider()
        st.markdown("##### ✏️ 修改列")
        _col = st.selectbox("列", current_columns, key="ddl_mod_col")
        _op = st.radio("操作",
            ["改类型", "改默认值", "设为 NOT NULL", "取消 NOT NULL"],
            horizontal=True, key="ddl_mod_op")
        _arg = st.text_input("参数（改类型填类型名，改默认值填表达式）",
                              key="ddl_mod_arg")
        if st.button("应用修改", type="primary", key="ddl_mod_btn"):
            try:
                if _op == "改类型":
                    con.cursor().execute(
                        f"ALTER TABLE {FQTN} ALTER COLUMN {_col} SET DATA TYPE {_arg}")
                elif _op == "改默认值":
                    con.cursor().execute(
                        f"ALTER TABLE {FQTN} ALTER COLUMN {_col} SET DEFAULT {_arg}")
                elif _op == "设为 NOT NULL":
                    con.cursor().execute(
                        f"ALTER TABLE {FQTN} ALTER COLUMN {_col} SET NOT NULL")
                else:
                    con.cursor().execute(
                        f"ALTER TABLE {FQTN} ALTER COLUMN {_col} DROP NOT NULL")
                st.success(f"✅ 已修改 {_col}")
                st.rerun()
            except Exception as e:
                st.error(f"❌ DuckLake 可能不支持此 DDL：{e}")

        st.divider()
        st.markdown("##### ➖ 删除列")
        _drop = st.selectbox("选择列", current_columns, key="ddl_drop_col")
        if st.button("确认删除", type="primary", key="ddl_drop_btn"):
            if tgt == "fs_data" and _drop in KEY_COLS:
                st.error("❌ fs_data 的核心列不可删")
            else:
                try:
                    con.cursor().execute(
                        f"ALTER TABLE {FQTN} DROP COLUMN {_drop}")
                    st.success(f"✅ 已删除 {_drop}")
                    st.rerun()
                except Exception as e:
                    st.error(f"❌ {e}")

    # ---------- 3. 索引 / 视图 ----------
    with _t3:
        st.markdown("##### 索引")
        _idx_name = st.text_input("索引名", key="ddl_idx_name")
        _idx_cols = st.text_input("列（逗号分隔）", key="ddl_idx_cols")
        if st.button("创建索引", key="ddl_idx_create"):
            try:
                con.cursor().execute(
                    f"CREATE INDEX {_idx_name} ON {FQTN} ({_idx_cols})")
                st.success(f"✅ 索引 {_idx_name} 创建成功")
                st.rerun()
            except Exception as e:
                st.error(f"❌ {e}")

        st.divider()
        st.markdown("##### 视图")
        _vw_name = st.text_input("视图名", key="ddl_vw_name")
        _vw_sql = st.text_area("SELECT 语句", height=120, key="ddl_vw_sql")
        if st.button("创建/替换视图", key="ddl_vw_create"):
            try:
                con.cursor().execute(
                    f"CREATE OR REPLACE VIEW {ALIAS}.main.{_vw_name} AS {_vw_sql}")
                st.success(f"✅ 视图 {_vw_name} 已创建")
                st.rerun()
            except Exception as e:
                st.error(f"❌ {e}")

    # ---------- 4. DDL 导出 ----------
    with _t4:
        try:
            _cols = con.cursor().execute(f"DESCRIBE {FQTN}").df()
            _lines = [f"CREATE TABLE {tgt} ("]
            for _, r in _cols.iterrows():
                _lines.append(f"  {r['column_name']} {r['column_type']},")
            _lines[-1] = _lines[-1].rstrip(",")
            _lines.append(");")
            _ddl = "\n".join(_lines)
            st.code(_ddl, language="sql")
            st.download_button("⬇️ 下载 DDL", _ddl,
                file_name=f"{tgt}_schema.sql", mime="text/plain",
                key="ddl_export_btn")
        except Exception as e:
            st.error(f"❌ {e}")

    # ---------- 5. DuckLake 元数据 ----------
    with _t5:
        try:
            st.markdown("**ducklake_table_info**")
            ti_df = con.cursor().execute(
                f"CALL ducklake_table_info('{ALIAS}')").df()
            st.dataframe(ti_df, width='stretch', hide_index=True)
        except Exception as e:
            st.warning(f"table_info 不可用：{e}")

        try:
            st.markdown("**ducklake_snapshot**")
            sn_df = con.cursor().execute(
                f"CALL ducklake_snapshots('{ALIAS}')").df()
            st.dataframe(sn_df.tail(30), width='stretch',
                          hide_index=True)
        except Exception as e:
            st.warning(f"snapshots 不可用：{e}")

    # ---------- 6. 危险区 ----------
    with _t6:
        st.error("以下操作不可逆。")
        _danger = st.radio("操作",
            ["重命名表", "清空表（TRUNCATE）", "复制表", "DROP TABLE"],
            key="ddl_danger_op")
        if _danger == "重命名表":
            _new_name = st.text_input("新表名", key="ddl_rn_new")
            if st.button("确认重命名", type="primary", key="ddl_rn_btn"):
                try:
                    con.cursor().execute(
                        f"ALTER TABLE {FQTN} RENAME TO {_new_name}")
                    st.success("✅ 已重命名")
                    st.rerun()
                except Exception as e:
                    st.error(f"❌ {e}")
        elif _danger == "清空表（TRUNCATE）":
            _ok = st.checkbox(f"确认清空 {tgt} 全表数据", key="ddl_truncate_ok")
            if st.button("执行清空", type="primary",
                         disabled=not _ok, key="ddl_truncate_btn"):
                con.cursor().execute(f"DELETE FROM {FQTN}")
                st.success("✅ 已清空")
                st.rerun()
        elif _danger == "复制表":
            _copy = st.text_input("新表名", key="ddl_copy_new")
            if st.button("确认复制", type="primary", key="ddl_copy_btn"):
                try:
                    con.cursor().execute(
                        f"CREATE TABLE {ALIAS}.main.{_copy} AS SELECT * FROM {FQTN}")
                    st.success("✅ 已复制")
                    st.rerun()
                except Exception as e:
                    st.error(f"❌ {e}")
        else:
            _ok = st.checkbox(f"确认 DROP TABLE {tgt}（数据不可恢复）",
                               key="ddl_drop_table_ok")
            if st.button("执行 DROP TABLE", type="primary",
                         disabled=not _ok, key="ddl_drop_table_btn"):
                try:
                    con.cursor().execute(f"DROP TABLE {FQTN}")
                    st.success("✅ 已删除表")
                    st.rerun()
                except Exception as e:
                    st.error(f"❌ {e}")