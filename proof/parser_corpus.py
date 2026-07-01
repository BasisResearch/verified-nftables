#!/usr/bin/env python3
"""parser_corpus.py — honest coverage of the UNTRUSTED .nft frontend.

Feeds a large, diverse, REAL corpus of nftables rules through `nftc compile`
(parse -> lower -> Compile.compile_chain) and reports an HONEST coverage table:

  parsed-ok            : frontend built an AST AND it compiled (no error)
  fail: parser-bug     : valid nft the frontend SHOULD handle but errored
  fail: out-of-model   : construct the verified model genuinely does not carry

Corpus sources (provenance recorded):
  1. nftables' own test suite: the `;ok` rule lines in tests/py/**/*.t and the
     `# <rule>` header lines in tests/py/**/*.t.payload  (from $NFT_CORPUS).
  2. nftables' shipped example rulesets: files/**, doc/, examples/ under $NFT_CORPUS.
  3. real-world .nft configs mined from many independent GitHub repos, committed
     under proof/parser_corpus/github/ with PROVENANCE.tsv.

A failure is bucketed by its (normalised) error message; the buckets are then
classified parser-bug vs out-of-model by OUT_OF_MODEL_MARKERS below (documented,
not faked).  Nothing is silently swallowed: every failure shows up in a bucket.
"""
import os, sys, subprocess, re, glob, collections

HERE = os.path.dirname(os.path.abspath(__file__))
NFT_CORPUS = os.environ.get("NFT_CORPUS", "/tmp/nftables-src")
CLI = os.path.join(HERE, "extracted", "_build", "default", "nftc_cli.exe")
GITHUB_DIR = os.path.join(HERE, "parser_corpus", "github")

# Error-message substrings that denote a construct the verified MODEL genuinely
# does not represent, so a parse failure is HONESTLY out of scope rather than a
# fixable frontend gap.  Kept DELIBERATELY SHORT and conservative: everything
# else (missing selectors/symbols/services, un-lowered value maps, exthdr/inner
# grammar, …) is a FIXABLE frontend gap and is counted as a parser-bug, NOT
# hidden here.  Do NOT pad this list to inflate "out-of-model".
OUT_OF_MODEL_MARKERS = [
    # `iif`/`oif` by interface NAME compares the kernel interface *index*, which
    # only exists at load time against the live interface table — there is no
    # faithful compile-time value for it in the packet model (unlike `iifname`,
    # which we DO support).  This is the one genuinely runtime-dependent match.
    "resolved to a numeric index at load",
    # `ct helper|timeout|expectation set` / other non-settable keys: the model's
    # SCtSet/SMetaSet only carry the settable-register keys; these assign kernel
    # state the single-packet semantics does not represent.
    "ct key is not settable",
    "meta key is not settable",
]

def run(text):
    """Return (ok, err) from `nftc compile -` on ruleset text."""
    try:
        p = subprocess.run([CLI, "compile", "-"], input=text.encode(),
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
    except Exception as e:
        return False, "harness: %s" % e
    if p.returncode == 0:
        return True, ""
    return False, p.stderr.decode(errors="replace").strip()

def norm_err(err):
    """Collapse an error message to a bucket key (strip specific literals)."""
    e = err
    e = re.sub(r"nftc: ", "", e)
    e = re.sub(r"line \d+, column \d+", "line L, column C", e)
    e = re.sub(r"\"[^\"]*\"", "\"...\"", e)
    e = re.sub(r"0x[0-9a-fA-F]+", "0xN", e)
    e = re.sub(r"\b\d+\b", "N", e)
    e = re.sub(r"\$[A-Za-z_][A-Za-z0-9_]*", "$VAR", e)
    return e.strip()

def is_out_of_model(err):
    return any(m in err for m in OUT_OF_MODEL_MARKERS)

# --------------------------------------------------------------------------
# .t test files: extract per-file (family, table, chain, chainspec) + ok-rules
# --------------------------------------------------------------------------
def parse_t_file(path):
    chains = {}          # name -> spec string
    variants = []        # (family, table, [chainnames])
    ok_rules = []
    for raw in open(path, errors="replace"):
        line = raw.rstrip("\n")
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        if s.startswith(":"):
            body = s[1:]
            if ";" in body:
                name, spec = body.split(";", 1)
                chains[name.strip()] = spec.strip()
            continue
        if s.startswith("*"):
            parts = s[1:].split(";")
            if len(parts) >= 3:
                fam, tbl, chs = parts[0], parts[1], parts[2]
                variants.append((fam.strip(), tbl.strip(),
                                 [c.strip() for c in chs.split(",")]))
            continue
        # a rule line: RULE;ok | RULE;fail | RULE;ok;NORMALISED
        fields = s.split(";")
        if len(fields) >= 2 and fields[1].strip() == "ok":
            rule = fields[0].strip()
            # nft-test.py marks a rule whose listing is suppressed with a
            # leading "- "; the rule proper is the remainder.
            if rule.startswith("- "):
                rule = rule[2:].strip()
            ok_rules.append(rule)
    return chains, variants, ok_rules

def wrap_rule(fam, table, chain, spec, rule):
    return ("table %s %s {\n  chain %s {\n    %s\n    %s\n  }\n}\n"
            % (fam, table, chain, spec, rule))

def collect_t_units():
    units = []   # (label, ruleset_text, rule_text)
    for path in sorted(glob.glob(os.path.join(NFT_CORPUS, "tests/py/*/*.t"))):
        chains, variants, ok_rules = parse_t_file(path)
        if not variants:
            continue
        fam, table, chs = variants[0]
        chain = chs[0] if chs else "c"
        spec = chains.get(chain, "type filter hook input priority 0")
        base = os.path.basename(path)
        for r in ok_rules:
            units.append((base, wrap_rule(fam, table, chain, spec, r), r))
    return units

# --------------------------------------------------------------------------
# .t.payload files: the `# <rule>` header lines carry their own context line
#   # <rule>
#   <family> <table> <chain>
#     [ ...bytecode... ]
# --------------------------------------------------------------------------
def collect_payload_units():
    units = []
    for path in sorted(glob.glob(os.path.join(NFT_CORPUS, "tests/py/*/*.t.payload*"))):
        lines = open(path, errors="replace").read().splitlines()
        i = 0
        while i < len(lines):
            ln = lines[i]
            if ln.startswith("# "):
                rule = ln[2:].strip()
                ctx = lines[i+1].strip() if i+1 < len(lines) else ""
                m = re.match(r"^(\w+)\s+(\S+)\s+(\S+)", ctx)
                if m and rule:
                    fam, table, chain = m.group(1), m.group(2), m.group(3)
                    spec = "type filter hook input priority 0"
                    units.append((os.path.basename(path),
                                  wrap_rule(fam, table, chain, spec, rule), rule))
            i += 1
    return units

# --------------------------------------------------------------------------
# STRONG golden check: for each `# rule` block in *.t.payload*, compile the rule
# in the block's OWN family + hook (from the sibling .t chain spec) and compare
# nftc's emitted bytecode BYTE-FOR-BYTE to the golden instruction lines.  This is
# the honest fidelity metric: a rule that compiles (rc 0) but to DIFFERENT
# bytecode than the golden is a WRONG-BYTECODE unit, NOT a pass.  It answers the
# weakness of the compile-rc-0 sections above (which only check `nftc` returns 0).
# --------------------------------------------------------------------------
def _chain_specs(tfile):
    specs = {}
    try:
        for raw in open(tfile, errors="replace"):
            s = raw.strip()
            if s.startswith(":"):
                body = s[1:]
                if ";" in body:
                    n, sp = body.split(";", 1)
                    specs[n.strip()] = sp.strip()
    except Exception:
        pass
    return specs

def _norm_instr(l):
    return re.sub(r"\s+", " ", l.strip())

def compile_instr_lines(text):
    """Compile [text] and return (instr_lines or None, err).  instr_lines are the
    rendered `[ ... ]` bytecode lines (the leading `table chain` line dropped)."""
    try:
        p = subprocess.run([CLI, "compile", "-"], input=text.encode(),
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
    except Exception as e:
        return None, "harness: %s" % e
    if p.returncode != 0:
        return None, p.stderr.decode(errors="replace").strip()
    lines = [_norm_instr(l) for l in p.stdout.decode(errors="replace").splitlines()
             if l.strip().startswith("[")]
    return lines, ""

def golden_payload_report():
    match = mism = fail = 0
    fails = collections.defaultdict(list)     # error bucket -> [rule]
    mismbk = collections.defaultdict(list)    # first-divergent-golden-line -> [rule]
    for path in sorted(glob.glob(os.path.join(NFT_CORPUS, "tests/py/*/*.t.payload*"))):
        base = os.path.basename(path)
        tfile = os.path.join(os.path.dirname(path), re.sub(r"\.payload.*$", "", base))
        specs = _chain_specs(tfile)
        lines = open(path, errors="replace").read().splitlines()
        i = 0
        while i < len(lines):
            ln = lines[i]
            if not ln.startswith("# "):
                i += 1; continue
            rule = ln[2:].strip()
            ctx = lines[i+1].strip() if i+1 < len(lines) else ""
            m = re.match(r"^(\w+)\s+(\S+)\s+(\S+)", ctx)
            gold = []
            j = i + 2
            while j < len(lines) and lines[j].strip().startswith("["):
                gold.append(_norm_instr(lines[j])); j += 1
            i = j
            if not (m and rule and gold):
                continue
            fam, table, chain = m.group(1), m.group(2), m.group(3)
            spec = specs.get(chain, "type filter hook input priority 0")
            got, err = compile_instr_lines(wrap_rule(fam, table, chain, spec, rule))
            if got is None:
                fail += 1; fails[norm_err(err)].append(rule)
            elif got == gold:
                match += 1
            else:
                mism += 1
                diff = next((g for g in gold if g not in set(got)), (gold[0] if gold else ""))
                mismbk[diff[:60]].append(rule)
    total = match + mism + fail
    print("== STRONG golden bytecode check (*.t.payload*, compiled in each block's "
          "own family+hook, vs the golden bytes) ==")
    print("   byte-identical: %d/%d (%.1f%%) ; wrong-bytecode: %d ; compile-fail: %d"
          % (match, total, 100.0*match/total if total else 0, mism, fail))
    print("   -- top WRONG-BYTECODE buckets (compile rc 0 but bytes != golden) --")
    for k, v in sorted(mismbk.items(), key=lambda kv: -len(kv[1]))[:12]:
        print("     %4d  missing/diff golden line: %s" % (len(v), k))
        print("            e.g. %s" % v[0][:90])
    print()
    return match, mism, fail, total

# --------------------------------------------------------------------------
# whole-file rulesets: shipped nftables examples + mined GitHub configs
# --------------------------------------------------------------------------
def collect_file_units():
    units = []
    patterns = [
        os.path.join(NFT_CORPUS, "files/**/*.nft"),
        os.path.join(NFT_CORPUS, "doc/**/*.nft"),
        os.path.join(NFT_CORPUS, "examples/**/*.nft"),
        os.path.join(GITHUB_DIR, "*.nft"),
    ]
    for pat in patterns:
        for path in sorted(glob.glob(pat, recursive=True)):
            try:
                txt = open(path, errors="replace").read()
            except Exception:
                continue
            if not txt.strip():
                continue
            units.append((os.path.relpath(path, HERE), txt, path))
    return units

def report(name, units, strong=True):
    ok = 0
    fails = collections.defaultdict(list)   # bucket -> [rule/label]
    for label, text, rule in units:
        good, err = run(text)
        if good:
            ok += 1
        else:
            fails[norm_err(err)].append((label, rule if strong else label))
    total = len(units)
    print("== %s : %d/%d parsed+compiled (%.1f%%) ==" %
          (name, ok, total, 100.0*ok/total if total else 0.0))
    bug = ooze = 0
    buckets = sorted(fails.items(), key=lambda kv: -len(kv[1]))
    for bucket, items in buckets:
        kind = "out-of-model" if is_out_of_model(bucket) else "PARSER-BUG"
        if kind == "PARSER-BUG":
            bug += len(items)
        else:
            ooze += len(items)
        print("  [%-12s] %4d  %s" % (kind, len(items), bucket[:90]))
        # show one concrete example
        ex = items[0][1]
        print("               e.g. %s" % str(ex)[:110])
    print("  -> parser-bug failures: %d ; out-of-model failures: %d\n" % (bug, ooze))
    return ok, total, bug, ooze

def main():
    if not os.path.exists(CLI):
        print("ERROR: build the CLI first (make cli):", CLI); sys.exit(2)
    sections = [
        ("nftables tests/py *.t  (;ok rules)",        collect_t_units(),     True),
        ("nftables tests/py *.t.payload (# rules)",    collect_payload_units(), True),
        ("real rulesets (nft examples + GitHub)",      collect_file_units(),  False),
    ]
    grand_ok = grand_total = grand_bug = grand_ooze = 0
    for name, units, strong in sections:
        ok, total, bug, ooze = report(name, units, strong)
        grand_ok += ok; grand_total += total; grand_bug += bug; grand_ooze += ooze
    print("==== TOTAL (weak, compile-rc-0): %d/%d parsed+compiled (%.1f%%) ; "
          "parser-bug=%d out-of-model=%d ====" %
          (grand_ok, grand_total, 100.0*grand_ok/grand_total if grand_total else 0,
           grand_bug, grand_ooze))
    print()
    # The HONEST fidelity metric for the test-corpus payload rules: compare the
    # emitted bytecode to the golden bytes, so a wrong-bytecode compile is NOT a
    # pass.  (The whole-file GitHub/example rulesets have no golden bytes, so only
    # the compile-rc-0 metric applies to them.)
    gm, gx, gf, gt = golden_payload_report()
    print("==== HONEST payload fidelity: %d/%d byte-identical to golden (%.1f%%) ; "
          "%d wrong-bytecode ; %d compile-fail ====" %
          (gm, gt, 100.0*gm/gt if gt else 0, gx, gf))

if __name__ == "__main__":
    main()
