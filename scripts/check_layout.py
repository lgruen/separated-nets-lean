#!/usr/bin/env python3
"""Mechanical Palomar layout checks for this Lean project (a local pre-flight, not the verifier).

Run from anywhere:   uv run --with pyyaml scripts/check_layout.py [CONFIG.json [METADATA.yaml]]
  (defaults: comparatorHeadline.json and palomar/headline/formalization.yaml, the Palomar entry;
  paths relative to the root)
Checks (PalomarPolicy CONTRIBUTING.md §2.1-2.5, §3.1-3.2):
  * every .lean file outside .lake/.git uses the module system and has <= 10,000 lines;
    no .lean symlinks;
  * Challenge <= 1,000 lines and <= 100 KiB (warn above 300 lines / 32 KiB); its direct imports
    are Mathlib-only;
  * comparator.json: one object, exactly the allowed keys, nonempty theorem names that occur as
    theorems in the Challenge, permitted axioms within {propext, Quot.sound, Classical.choice};
  * exactly one Lakefile (valid TOML), committed manifest with github URLs pinned to 40-hex
    SHAs, lean-toolchain equal to the resolved Mathlib checkout's toolchain;
  * no compiled artifacts outside .lake, no .gitmodules;
  * LICENSE present and its SPDX id (MIT detection only) equals formalization.yaml
    project.license; formalization.yaml mechanically required fields and source-origin rule.
Exit status 0 iff no ERROR.
"""
import json
import os
import re
import subprocess
import sys
import tomllib

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
errors, warnings, oks = [], [], []


def err(msg):
    errors.append(msg)


def ok(msg):
    oks.append(msg)


def physical_lines(data: bytes) -> int:
    if not data:
        return 0
    n = data.count(b"\n")
    return n if data.endswith(b"\n") else n + 1


def strip_leading_comments(text: str) -> str:
    """Remove leading blank lines, `--` line comments and (nested) `/- -/` block comments."""
    i, n = 0, len(text)
    while i < n:
        if text[i].isspace():
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j + 1
        elif text.startswith("/-", i) and not text.startswith("/-!", i) \
                and not text.startswith("/--", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth, i = depth + 1, i + 2
                elif text.startswith("-/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
        else:
            break
    return text[i:]


# ---------------------------------------------------------------- .lean files
lean_files = []
for dp, dns, fns in os.walk(ROOT):
    dns[:] = [d for d in dns if d not in (".lake", ".git")]
    for fn in fns:
        p = os.path.join(dp, fn)
        rel = os.path.relpath(p, ROOT)
        if re.search(r"\.(olean|ilean|a|bc|dll|dylib|o|obj|so|trace)$", fn):
            err(f"compiled artifact outside .lake: {rel}")
        if fn == ".gitmodules":
            err(f"git submodules file present: {rel}")
        if fn.endswith(".lean"):
            if os.path.islink(p):
                err(f".lean symlink: {rel}")
                continue
            lean_files.append(rel)

maxlines = 0
for rel in sorted(lean_files):
    data = open(os.path.join(ROOT, rel), "rb").read()
    nl = physical_lines(data)
    maxlines = max(maxlines, nl)
    if nl > 10000:
        err(f"{rel}: {nl} lines > 10,000")
    if os.path.basename(rel) == "lakefile.lean":
        continue
    head = strip_leading_comments(data.decode("utf-8"))
    if not re.match(r"module\b", head):
        err(f"{rel}: does not start with the `module` header")
ok(f"{len(lean_files)} .lean files: all use `module`, max {maxlines} lines (limit 10,000)"
   if not any("module" in e or "lines >" in e for e in errors) else "lean file checks run")

# ---------------------------------------------------------------- comparator.json
CFG_REL = sys.argv[1] if len(sys.argv) > 1 else "comparatorHeadline.json"
META_REL = sys.argv[2] if len(sys.argv) > 2 else "palomar/headline/formalization.yaml"
if os.path.basename(META_REL) != "formalization.yaml":
    err(f"metadata basename must be exactly formalization.yaml: {META_REL}")
cfg_path = os.path.join(ROOT, CFG_REL)
cfg = json.load(open(cfg_path))
if os.path.getsize(cfg_path) > 1 << 20:
    err(f"{CFG_REL} > 1 MiB")
if not isinstance(cfg, dict):
    err("comparator.json is not one object")
required = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
allowed = required | {"definition_names", "enable_nanoda"}
if not required <= cfg.keys():
    err(f"comparator.json missing keys {sorted(required - cfg.keys())}")
if not cfg.keys() <= allowed:
    err(f"comparator.json has disallowed keys {sorted(cfg.keys() - allowed)}")
mod_re = r"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*"
for k in ("challenge_module", "solution_module"):
    if not re.fullmatch(mod_re, cfg.get(k, "")):
        err(f"comparator.json {k} is not a dotted module name")
if cfg.get("challenge_module") == cfg.get("solution_module"):
    err("challenge and solution modules coincide")
thms = cfg.get("theorem_names", [])
if not thms or not all(isinstance(t, str) and t for t in thms):
    err("theorem_names must be a nonempty list of nonempty strings")
if not all(isinstance(t, str) and t for t in cfg.get("definition_names", [])):
    err("definition_names entries must be nonempty strings")
if not set(cfg.get("permitted_axioms", [])) <= {"propext", "Quot.sound", "Classical.choice"}:
    err(f"permitted_axioms not within the allowed three: {cfg.get('permitted_axioms')}")

# ---------------------------------------------------------------- Challenge
chal_rel = cfg["challenge_module"].replace(".", "/") + ".lean"
chal = open(os.path.join(ROOT, chal_rel), "rb").read()
cl, ckib = physical_lines(chal), len(chal) / 1024
if cl > 1000 or len(chal) > 100 * 1024:
    err(f"Challenge {cl} lines / {ckib:.1f} KiB exceeds 1,000 lines / 100 KiB")
if cl > 300 or len(chal) > 32 * 1024:
    warnings.append(f"Challenge {cl} lines / {ckib:.1f} KiB is above the 300-line / 32 KiB "
                    "audit-size warning threshold (hard limit 1,000 / 100 KiB)")
ctext = chal.decode("utf-8")
imports = re.findall(r"^(?:public\s+)?(?:meta\s+)?import\s+(\S+)", ctext, re.M)
bad = [i for i in imports if not (i == "Mathlib" or i.startswith("Mathlib."))]
if bad:
    err(f"Challenge imports non-Mathlib modules: {bad}")
ns = re.findall(r"^namespace\s+(\S+)", ctext, re.M)
missing = 0
for t in thms:
    short = t.split(".")[-1]
    prefix = ".".join(t.split(".")[:-1])
    if not re.search(rf"^theorem\s+{re.escape(short)}\b", ctext, re.M) or \
            (prefix and prefix not in ns):
        err(f"theorem {t} not found in {chal_rel}")
        missing += 1
ok(f"Challenge: {cl} lines, {ckib:.1f} KiB, imports {imports}, "
   f"{len(thms) - missing}/{len(thms)} comparator theorems present")

# ---------------------------------------------------------------- Lake files
has_toml = os.path.isfile(os.path.join(ROOT, "lakefile.toml"))
has_lean = os.path.isfile(os.path.join(ROOT, "lakefile.lean"))
if has_toml + has_lean != 1:
    err("need exactly one of lakefile.toml / lakefile.lean")
if has_toml:
    lf = os.path.join(ROOT, "lakefile.toml")
    if os.path.getsize(lf) > 1 << 20:
        err("lakefile.toml > 1 MiB")
    lake = tomllib.load(open(lf, "rb"))
man_path = os.path.join(ROOT, "lake-manifest.json")
if not os.path.isfile(man_path):
    err("lake-manifest.json missing")
man = json.load(open(man_path))
for pkg in man.get("packages", []):
    if pkg.get("type") == "git":
        if not re.fullmatch(r"https://github\.com/[^/?#@]+/[^/?#@]+", pkg["url"]):
            err(f"manifest package {pkg['name']}: url {pkg['url']} not a plain github URL")
        if not re.fullmatch(r"[0-9a-f]{40}", pkg["rev"]):
            err(f"manifest package {pkg['name']}: rev not a 40-hex SHA")
    else:
        err(f"manifest package {pkg.get('name')} is not a git package")
tc = open(os.path.join(ROOT, "lean-toolchain")).read().strip()
if not re.fullmatch(r"leanprover/lean4:v\d+\.\d+\.\d+(-rc\d+)?", tc):
    err(f"lean-toolchain malformed: {tc}")
ml = next((p for p in man["packages"] if p["name"] == "mathlib"), None)
if ml:
    mdir = os.path.join(ROOT, ".lake", "packages", "mathlib")
    try:
        head = subprocess.run(["git", "-C", mdir, "rev-parse", "HEAD"], capture_output=True,
                              text=True, check=True).stdout.strip()
        mtc = open(os.path.join(mdir, "lean-toolchain")).read().strip()
        if head != ml["rev"]:
            err(f"Mathlib checkout {head} != manifest rev {ml['rev']}")
        if mtc != tc:
            err(f"lean-toolchain {tc} != Mathlib's {mtc}")
        req = [r for r in lake.get("require", []) if r.get("name") == "mathlib"] if has_toml else []
        ok(f"toolchain {tc} == Mathlib@{ml['rev'][:12]} toolchain; lakefile mathlib rev "
           f"{req[0].get('rev') if req else '?'}; manifest inputRev {ml.get('inputRev')}")
    except (subprocess.CalledProcessError, FileNotFoundError) as e:
        warnings.append(f"could not inspect Mathlib checkout ({e}); toolchain match unchecked")

# ---------------------------------------------------------------- licence + metadata
lic = [f for f in os.listdir(ROOT) if re.fullmatch(
    r"(license|licence|copying|unlicense|ofl)(\.md|\.markdown|\.txt)?", f, re.I)]
spdx = None
if len(lic) != 1:
    err(f"need exactly one licence file at the project root, found {lic}")
else:
    lt = open(os.path.join(ROOT, lic[0]), encoding="utf-8").read()
    if lt.strip().startswith("MIT License") and "Permission is hereby granted, free of charge" in lt:
        spdx = "MIT"
    else:
        warnings.append(f"{lic[0]}: not recognised as MIT by this script (only MIT is detected)")
try:
    import yaml
except ImportError:
    err("pyyaml unavailable: run with `uv run --with pyyaml`")
    yaml = None
if yaml:
    fy_path = os.path.join(ROOT, META_REL)
    if os.path.getsize(fy_path) > 256 * 1024:
        err("formalization.yaml > 256 KiB")

    class NoDup(yaml.SafeLoader):
        pass

    def no_dup(loader, node, deep=False):
        keys = [loader.construct_object(k, deep=deep) for k, _ in node.value]
        if len(keys) != len(set(keys)):
            raise ValueError(f"duplicate keys in mapping at line {node.start_mark.line + 1}")
        if any(k.tag == "tag:yaml.org,2002:merge" for k, _ in node.value):
            raise ValueError("YAML merge keys are not accepted")
        return loader.construct_mapping(node, deep)

    NoDup.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, no_dup)
    fy = yaml.load(open(fy_path, encoding="utf-8"), Loader=NoDup)
    pj = fy.get("project", {})

    def nonempty_str(x):
        return isinstance(x, str) and x.strip() != ""

    if not (nonempty_str(pj.get("name")) and len(pj["name"]) <= 300):
        err("project.name missing or > 300 chars")
    if not (nonempty_str(pj.get("description")) and len(pj["description"]) <= 10000):
        err("project.description missing or > 10,000 chars")
    def orcid_ok(o):
        # bare iD or https://orcid.org URL, ISO 7064 mod 11-2 check digit (as Palomar's contract)
        m = re.fullmatch(r"(?:https://orcid\.org/)?(\d{4})-(\d{4})-(\d{4})-(\d{3}[\dX])",
                         str(o).strip())
        if not m:
            return False
        d, t = "".join(m.groups()), 0
        for ch in d[:-1]:
            t = (t + int(ch)) * 2
        r = (12 - t % 11) % 11
        return d[-1] == ("X" if r == 10 else str(r))

    def person_ok(a):
        # a name, or a mapping {name, orcid?, github?} (Palomar submission contract)
        if nonempty_str(a):
            return True
        return isinstance(a, dict) and nonempty_str(a.get("name")) and \
            ("orcid" not in a or orcid_ok(a["orcid"]))

    for key in ("authors", "responsible_maintainers"):
        v = pj.get(key)
        if not (isinstance(v, list) and v and all(person_ok(a) for a in v)):
            err(f"project.{key} must be a nonempty list of names or {{name, orcid}} mappings "
                "(valid ORCID iD)")
    if spdx and pj.get("license") != spdx:
        err(f"project.license {pj.get('license')!r} != LICENSE SPDX {spdx!r}")
    cl_ = fy.get("classification", {})
    ax = cl_.get("arxiv", [])
    if not (isinstance(ax, list) and 1 <= len(ax) <= 8 and len(set(ax)) == len(ax)):
        err("classification.arxiv must have 1-8 distinct codes")
    msc = cl_.get("msc2020", [])
    if not (isinstance(msc, list) and len(msc) <= 8 and len(set(msc)) == len(msc)):
        err("classification.msc2020 must have <= 8 distinct codes")
    meth = fy.get("automation", {}).get("methods")
    if not (isinstance(meth, list) and meth and all(nonempty_str(m.get("method")) for m in meth)):
        err("automation.methods must be a nonempty list with nonempty `method`")
    if not nonempty_str(fy.get("review", {}).get("status")):
        err("review.status missing")
    srcs = fy.get("sources")
    rels = {"formalizes", "adapts", "independently-proves", "background", "other"}
    types = {"paper", "book", "web discussion", "folklore", "original-proof", "other"}
    if not (isinstance(srcs, list) and srcs):
        err("sources must be a nonempty list")
    else:
        for s in srcs:
            if not nonempty_str(s.get("title")) or s.get("relationship") not in rels:
                err(f"source {s.get('title')!r}: missing title or bad relationship")
            sa = s.get("authors")
            if sa is not None and not (isinstance(sa, list) and all(person_ok(a) for a in sa)):
                err(f"source {s.get('title')!r}: authors must be names or {{name, orcid}} "
                    "mappings (valid ORCID iD)")
            if "type" in s and s["type"] not in types:
                err(f"source {s.get('title')!r}: bad type {s['type']!r}")
        orig = [s for s in srcs if s.get("type") == "original-proof"]
        subst = [s for s in srcs if s.get("relationship") in
                 ("formalizes", "adapts", "independently-proves")]
        if orig and (subst or any(s["relationship"] != "other" for s in orig)):
            err("original-proof source combined with a substantive relationship")
        if not orig and not subst:
            err("no source with relationship formalizes/adapts/independently-proves")
        ok(f"sources: origin = {'original' if orig else 'source-based'}")
    cfgs = {r.get("comparator_config") for r in
            (fy.get("status", {}) or {}).get("main_results", []) or []}
    if cfgs and cfgs != {os.path.basename(CFG_REL)}:
        err(f"main_results comparator_config {sorted(map(str, cfgs))} != {CFG_REL}")
    # the metadata must describe the compared theorems of this configuration (V14 stage S6: a
    # re-targeted entry must not keep the declarations of the old one)
    decls = [r.get("declaration") for r in
             (fy.get("status", {}) or {}).get("main_results", []) or []]
    if decls and set(decls) != set(thms):
        err(f"status.main_results declarations {sorted(map(str, decls))} != theorem_names "
            f"{sorted(thms)}")
    al = fy.get("alignment", {}) or {}
    alean = [st.get("lean") for st in al.get("statements", []) or []]
    if alean and not set(alean) <= set(thms):
        err(f"alignment lean names {sorted(set(map(str, alean)) - set(thms))} not in theorem_names")
    if al.get("namespace") and not all(t.startswith(al["namespace"] + ".") for t in thms):
        err(f"alignment.namespace {al['namespace']!r} does not prefix every compared theorem")
    if decls:
        ok(f"metadata names the {len(decls)} compared theorem(s) of {CFG_REL}")
    for r in fy.get("related_formalizations", []) or []:
        if not nonempty_str(r.get("id")):
            err("related_formalizations entry without id")
    ok(f"{META_REL} for {CFG_REL}: version {fy.get('version')}, license {pj.get('license')}, "
       f"review.status {fy.get('review', {}).get('status')!r}")

for m in oks:
    print("OK     ", m)
for m in warnings:
    print("WARN   ", m)
for m in errors:
    print("ERROR  ", m)
print(f"\n{len(errors)} error(s), {len(warnings)} warning(s)")
sys.exit(1 if errors else 0)
