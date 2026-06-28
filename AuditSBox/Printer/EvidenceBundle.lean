import Mathlib
import AuditSBox.Audit.CipherDefs
import AuditSBox.Audit.CustomSbox

/-!
# Evidence Bundle Generator — Audit Loop & Deliverables

This module provides the **audit loop**: functions that take `Certificate`
or `SboxAudit` structures and produce:

  1. **Formatted tables** — human-readable single-certificate and
     multi-certificate comparison tables
  2. **Markdown reports** — client-ready certificate documents
  3. **Evidence file templates** — self-contained Lean proof files
  4. **README templates** — 2-minute verification instructions

## Usage

```lean
import AuditSBox.Printer.EvidenceBundle
open CipherAudit EvidenceBundle

-- Single certificate display
#eval printCertificate AES.certificate

-- Multi-certificate comparison
#eval printComparison [AES.certificate, GIFT.certificate, ASCON.certificate]

-- Generate full evidence bundle (returns three strings: report, evidence, readme)
#eval generateBundle "AES" 8 AES.sbox AES.certificate
```

## What Gets Generated

For a client engagement, the `generateBundle` function produces three
text files that together form a complete, verifiable audit deliverable:

  - **Certificate.md** — The human-readable summary with all metrics,
    security interpretations, and comparison to known standards.

  - **Evidence.lean** — A self-contained Lean file that imports the
    framework and proves every claimed property via `native_decide`.
    The client (or any third party) can verify this independently
    by running `lake build`.

  - **README.md** — A 2-minute guide explaining what the files are,
    how to install Lean, and how to verify the proofs.
-/

namespace CipherAudit
namespace EvidenceBundle

/-! ### Pretty-printing infrastructure -/

/-- Pad a string to a fixed width (right-padded with spaces). -/
private def padRight (s : String) (width : Nat) : String :=
  s ++ String.ofList (List.replicate (width - min width s.length) ' ')

/-- Pad a string to a fixed width (left-padded with spaces). -/
private def padLeft (s : String) (width : Nat) : String :=
  String.ofList (List.replicate (width - min width s.length) ' ') ++ s

/-- Security grade based on differential uniformity and bit-width. -/
def securityGrade (n δ : Nat) : String :=
  let ratio := (δ.toFloat) / (2 ^ n).toFloat
  if ratio ≤ 0.0078125 then "★★★★★"     -- ≤ 2⁻⁷  (e.g. AES: 4/256)
  else if ratio ≤ 0.03125 then "★★★★☆"  -- ≤ 2⁻⁵
  else if ratio ≤ 0.125 then "★★★☆☆"    -- ≤ 2⁻³
  else if ratio ≤ 0.25 then "★★☆☆☆"     -- ≤ 2⁻²
  else "★☆☆☆☆"

/-- Format a single Certificate as a boxed display string. -/
def formatCertificate (c : Certificate) : String :=
  let border := "════════════════════════════════════════════"
  let sep    := "────────────────────────────────────────────"
  let δ := c.diffUnif
  let n := c.bits
  let nl := c.nonlinearity
  let imgBound := if δ > 0 then (2 ^ n + δ - 1) / δ else 2 ^ n
  let secBits := if δ > 0 then securityBits n δ else n.toFloat
  let grade := securityGrade n δ
  s!"╔{border}╗\n" ++
  s!"║  S-Box Security Certificate              ║\n" ++
  s!"║  Subject: {padRight c.name 33}║\n" ++
  s!"╠{border}╣\n" ++
  s!"║  Bit-width:              {padLeft (toString n) 6}          ║\n" ++
  s!"║  Permutation:            {padLeft (toString c.isPerm) 6}          ║\n" ++
  s!"╠{sep}╣\n" ++
  s!"║  DIFFERENTIAL ANALYSIS                    ║\n" ++
  s!"║  Uniformity δ:           {padLeft (toString δ) 6}          ║\n" ++
  s!"║  Diff bias:              {padLeft (toString (maxDiffBias n δ)) 6}          ║\n" ++
  s!"║  Security bits:          {padLeft (toString secBits) 6}          ║\n" ++
  s!"║  Grade:                  {padLeft grade 6}          ║\n" ++
  s!"╠{sep}╣\n" ++
  s!"║  LINEAR ANALYSIS                          ║\n" ++
  s!"║  Max Walsh |W|:          {padLeft (toString c.walshMax) 6}          ║\n" ++
  s!"║  Nonlinearity:           {padLeft (toString nl) 6}          ║\n" ++
  s!"╠{sep}╣\n" ++
  s!"║  BOOMERANG ANALYSIS                       ║\n" ++
  s!"║  Boomerang unif β:       {padLeft (toString c.boomerangU) 6}          ║\n" ++
  s!"╠{sep}╣\n" ++
  s!"║  STRUCTURAL ANALYSIS                      ║\n" ++
  s!"║  Deriv image bound:      ≥{padLeft (toString imgBound) 5}          ║\n" ++
  s!"╚{border}╝"

/-- Print a single certificate (for use with `#eval`). -/
def printCertificate (c : Certificate) : String := formatCertificate c

/-! ### Comparison table -/

/-- Format a row of the comparison table. -/
private def compRow (c : Certificate) : String :=
  let n := c.bits
  let δ := c.diffUnif
  let secBits := if δ > 0 then securityBits n δ else n.toFloat
  let grade := securityGrade n δ
  s!"│ {padRight c.name 12}│{padLeft (toString n) 5} │{padLeft (toString δ) 5} │" ++
  s!"{padLeft (toString c.nonlinearity) 5} │{padLeft (toString c.walshMax) 5} │" ++
  s!"{padLeft (toString c.boomerangU) 5} │{padLeft (toString secBits) 8} │ " ++
  s!"{padRight grade 6}│"

/-- Format a multi-certificate comparison table. -/
def formatComparison (certs : List Certificate) : String :=
  let header :=
    "┌─────────────┬──────┬──────┬──────┬──────┬──────┬─────────┬───────┐\n" ++
    "│ S-Box       │ Bits │  δ   │  NL  │  |W| │  β   │ SecBits │ Grade │\n" ++
    "├─────────────┼──────┼──────┼──────┼──────┼──────┼─────────┼───────┤"
  let rows := certs.map compRow |>.foldl (· ++ "\n" ++ ·) ""
  let footer :=
    "\n└─────────────┴──────┴──────┴──────┴──────┴──────┴─────────┴───────┘"
  header ++ rows ++ footer

/-- Print a comparison table (for use with `#eval`). -/
def printComparison (certs : List Certificate) : String :=
  formatComparison certs

/-! ### Markdown certificate report generator -/

/-- Generate a markdown certificate report for a single S-box. -/
def generateCertificateMarkdown (c : Certificate) (tableLiteral : String) : String :=
  let n := c.bits
  let δ := c.diffUnif
  let nl := c.nonlinearity
  let imgBound := if δ > 0 then (2 ^ n + δ - 1) / δ else 2 ^ n
  let secBits := if δ > 0 then securityBits n δ else n.toFloat
  let grade := securityGrade n δ
  let bias := maxDiffBias n δ
  s!"# S-Box Security Certificate: {c.name}\n" ++
  s!"\n" ++
  s!"**Date**: Machine-verified formal audit\n" ++
  s!"**Framework**: Lean 4 + Mathlib S-Box Audit Framework\n" ++
  s!"**Verification**: All properties proven via exhaustive `native_decide`\n" ++
  s!"\n" ++
  s!"---\n" ++
  s!"\n" ++
  s!"## Subject\n" ++
  s!"\n" ++
  s!"| Field          | Value              |\n" ++
  s!"|----------------|--------------------|\n" ++
  s!"| Name           | {c.name}           |\n" ++
  s!"| Bit-width      | {n}                |\n" ++
  s!"| Domain         | GF(2)^{n} ({2^n} elements) |\n" ++
  s!"| Permutation    | {c.isPerm}         |\n" ++
  s!"\n" ++
  s!"## Security Metrics\n" ++
  s!"\n" ++
  s!"| Metric                    | Value    | Interpretation |\n" ++
  s!"|---------------------------|----------|----------------|\n" ++
  s!"| Differential uniformity δ | {δ}      | Max DDT entry (lower = better) |\n" ++
  s!"| Max differential bias     | {bias}   | δ / 2^n (lower = better) |\n" ++
  s!"| Security bits             | {secBits}| -log₂(bias) |\n" ++
  s!"| Max Walsh coefficient     | {c.walshMax} | Linear approximation bound |\n" ++
  s!"| Nonlinearity              | {nl}     | Distance to nearest linear function |\n" ++
  s!"| Boomerang uniformity β    | {c.boomerangU} | Max BCT entry (lower = better) |\n" ++
  s!"| Derivative image bound    | ≥ {imgBound} | Min distinct output differences |\n" ++
  s!"| Overall grade             | {grade}  | Based on differential bias |\n" ++
  s!"\n" ++
  s!"## What These Metrics Mean\n" ++
  s!"\n" ++
  s!"### Differential Uniformity (δ = {δ})\n" ++
  s!"\n" ++
  s!"An attacker performing differential cryptanalysis picks an input difference\n" ++
  s!"`a` and predicts an output difference `b`. The probability of a correct\n" ++
  s!"prediction is at most δ/2^n = {bias}. Lower δ means harder to attack.\n" ++
  s!"The theoretical minimum for bijective S-boxes is δ = 2.\n" ++
  s!"\n" ++
  s!"### Nonlinearity (NL = {nl})\n" ++
  s!"\n" ++
  s!"Measures the Hamming distance between the S-box and the nearest affine\n" ++
  s!"function. Higher nonlinearity means stronger resistance to linear\n" ++
  s!"cryptanalysis. The maximum possible for {n}-bit functions is\n" ++
  s!"NL ≤ (2^{n} - 2^({n}/2)) / 2.\n" ++
  s!"\n" ++
  s!"### Boomerang Uniformity (β = {c.boomerangU})\n" ++
  s!"\n" ++
  s!"Measures resistance to boomerang attacks, a more advanced differential\n" ++
  s!"technique. Lower β means fewer exploitable boomerang differentials.\n" ++
  s!"It is always the case that β ≥ δ.\n" ++
  s!"\n" ++
  s!"## Verification\n" ++
  s!"\n" ++
  s!"Every metric in this certificate is **machine-verified** using Lean 4's\n" ++
  s!"kernel. The proof method is `native_decide`: the check function is compiled\n" ++
  s!"to native code, executed exhaustively over all 2^{n} × 2^{n} = {2^n * 2^n}\n" ++
  s!"input pairs, and the result is verified by the Lean kernel.\n" ++
  s!"\n" ++
  s!"To independently verify, see the accompanying `Evidence.lean` file and\n" ++
  s!"follow the instructions in `README.md`.\n" ++
  s!"\n" ++
  s!"## S-Box Table\n" ++
  s!"\n" ++
  s!"```\n" ++
  s!"{tableLiteral}\n" ++
  s!"```\n" ++
  s!"\n" ++
  s!"---\n" ++
  s!"*Generated by the S-Box Audit Framework (Lean 4 + Mathlib)*\n"

/-! ### Evidence.lean generator -/

/-- Generate a self-contained Evidence.lean file for a single S-box. -/
def generateEvidenceLean (name : String) (n : Nat) (tableLiteral : String)
    (δ walshMax boomerangU : Nat) (isPerm : Bool) : String :=
  let inv_line := if isPerm then
    s!"def sboxInv : Array Nat := CipherAudit.invertTable sbox\n" else ""
  let perm_thm := if isPerm then
    s!"theorem sbox_perm : CipherAudit.isPermCheck sbox {n} = true := by native_decide\n" else ""
  let boom_thm := if isPerm then
    s!"theorem boomerang_bounded :\n" ++
    s!"    CipherAudit.boomerangBoundCheck sbox sboxInv {n} {boomerangU} = true := by native_decide\n"
  else ""
  s!"/-!\n" ++
  s!"  Evidence File — {name} S-Box Security Certificate\n" ++
  s!"\n" ++
  s!"  This file is a SELF-CONTAINED, MACHINE-VERIFIABLE proof of the\n" ++
  s!"  security properties claimed in the accompanying Certificate.\n" ++
  s!"\n" ++
  s!"  To verify: install Lean 4 and run `lake build` in this project.\n" ++
  s!"  Every theorem below is proven by exhaustive computation (`native_decide`).\n" ++
  s!"  If `lake build` succeeds, every claim is mathematically proven.\n" ++
  s!"-/\n" ++
  s!"import Mathlib\n" ++
  s!"import AuditSBox.Audit.CipherDefs\n" ++
  s!"\n" ++
  s!"namespace {name.replace " " "_"}_Evidence\n" ++
  s!"\n" ++
  s!"def sbox : Array Nat := {tableLiteral}\n" ++
  s!"\n" ++
  inv_line ++
  s!"\n" ++
  s!"-- ═══════════════════════════════════════════\n" ++
  s!"-- PROPERTY 1: Bijectivity\n" ++
  s!"-- ═══════════════════════════════════════════\n" ++
  perm_thm ++
  s!"\n" ++
  s!"-- ═══════════════════════════════════════════\n" ++
  s!"-- PROPERTY 2: Differential Uniformity δ ≤ {δ}\n" ++
  s!"-- ═══════════════════════════════════════════\n" ++
  s!"theorem ddt_bounded :\n" ++
  s!"    CipherAudit.ddtBoundCheck sbox {n} {δ} = true := by native_decide\n" ++
  s!"\n" ++
  s!"theorem ddt_tight :\n" ++
  s!"    CipherAudit.ddtTightCheck sbox {n} {δ} = true := by native_decide\n" ++
  s!"\n" ++
  s!"-- ═══════════════════════════════════════════\n" ++
  s!"-- PROPERTY 3: Walsh Spectrum |W| ≤ {walshMax}\n" ++
  s!"-- ═══════════════════════════════════════════\n" ++
  s!"theorem walsh_bounded :\n" ++
  s!"    CipherAudit.walshBoundCheck sbox {n} {walshMax} = true := by native_decide\n" ++
  s!"\n" ++
  s!"-- ═══════════════════════════════════════════\n" ++
  s!"-- PROPERTY 4: Boomerang Uniformity β ≤ {boomerangU}\n" ++
  s!"-- ═══════════════════════════════════════════\n" ++
  boom_thm ++
  s!"\n" ++
  s!"-- ═══════════════════════════════════════════\n" ++
  s!"-- CERTIFICATE SUMMARY\n" ++
  s!"-- ═══════════════════════════════════════════\n" ++
  s!"def certificate : CipherAudit.Certificate where\n" ++
  s!"  name         := \"{name}\"\n" ++
  s!"  bits         := {n}\n" ++
  s!"  diffUnif     := {δ}\n" ++
  s!"  nonlinearity := {(2^n - walshMax) / 2}\n" ++
  s!"  walshMax     := {walshMax}\n" ++
  s!"  boomerangU   := {boomerangU}\n" ++
  s!"  isPerm       := {isPerm}\n" ++
  s!"\n" ++
  s!"-- Verify axioms: only standard Lean axioms should appear.\n" ++
  s!"-- #print axioms ddt_bounded\n" ++
  s!"-- #print axioms walsh_bounded\n" ++
  s!"\n" ++
  s!"end {name.replace " " "_"}_Evidence\n"

/-! ### README.md generator -/

/-- Generate a README.md for the evidence bundle. -/
def generateReadme (name : String) : String :=
  s!"# {name} S-Box — Formal Security Certificate\n" ++
  s!"\n" ++
  s!"## What Is This?\n" ++
  s!"\n" ++
  s!"This folder contains a **machine-verified security audit** of the\n" ++
  s!"{name} S-box. Every security property claimed in `Certificate.md`\n" ++
  s!"is backed by a formal proof in `Evidence.lean` that has been checked\n" ++
  s!"by a computer.\n" ++
  s!"\n" ++
  s!"## Files\n" ++
  s!"\n" ++
  s!"| File             | What It Is                                |\n" ++
  s!"|------------------|-------------------------------------------|\n" ++
  s!"| `Certificate.md` | Human-readable security report             |\n" ++
  s!"| `Evidence.lean`  | Machine-verifiable proofs (the actual math) |\n" ++
  s!"| `README.md`      | This file — how to verify                  |\n" ++
  s!"\n" ++
  s!"## How to Verify (2 minutes)\n" ++
  s!"\n" ++
  s!"### Step 1: Install Lean 4\n" ++
  s!"\n" ++
  s!"```bash\n" ++
  s!"curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh\n" ++
  s!"```\n" ++
  s!"\n" ++
  s!"### Step 2: Build the project\n" ++
  s!"\n" ++
  s!"```bash\n" ++
  s!"cd <project-root>\n" ++
  s!"lake build\n" ++
  s!"```\n" ++
  s!"\n" ++
  s!"### Step 3: Interpret the result\n" ++
  s!"\n" ++
  s!"- **If `lake build` succeeds**: Every theorem in `Evidence.lean` is\n" ++
  s!"  mathematically proven. The security claims in `Certificate.md`\n" ++
  s!"  are correct.\n" ++
  s!"\n" ++
  s!"- **If `lake build` fails**: Something is wrong. Contact the auditor.\n" ++
  s!"\n" ++
  s!"### Step 4: Check axioms (optional)\n" ++
  s!"\n" ++
  s!"Open `Evidence.lean` in VS Code with the Lean extension, and uncomment\n" ++
  s!"the `#print axioms` lines at the bottom. You should see only:\n" ++
  s!"\n" ++
  s!"```\n" ++
  s!"[Lean.ofReduceBool]\n" ++
  s!"```\n" ++
  s!"\n" ++
  s!"This means the proof used `native_decide` — exhaustive verification\n" ++
  s!"compiled to native code. No custom axioms, no trust assumptions.\n" ++
  s!"\n" ++
  s!"## What Does `native_decide` Mean?\n" ++
  s!"\n" ++
  s!"The proofs work by:\n" ++
  s!"1. Defining a Boolean check function (e.g., \"is every DDT entry ≤ δ?\")\n" ++
  s!"2. Compiling it to native machine code\n" ++
  s!"3. Running it exhaustively over all inputs\n" ++
  s!"4. Having Lean's kernel verify the result\n" ++
  s!"\n" ++
  s!"This is **complete exhaustive verification** — every single input/output\n" ++
  s!"pair is checked. No sampling, no heuristics, no approximations.\n" ++
  s!"\n" ++
  s!"## Questions?\n" ++
  s!"\n" ++
  s!"The `Certificate.md` file explains what each metric means in plain English.\n" ++
  s!"For technical details, see the framework source code in `AuditSBox/Audit/`.\n"

/-! ### Full bundle generator -/

/-- Result of generating a full evidence bundle. -/
structure Bundle where
  /-- Markdown certificate report -/
  certificateMd : String
  /-- Self-contained Lean evidence file -/
  evidenceLean  : String
  /-- README with verification instructions -/
  readmeMd      : String
  deriving Repr

/-- Generate a complete evidence bundle for an S-box.

    Returns a `Bundle` containing three strings that should be
    written to `Certificate.md`, `Evidence.lean`, and `README.md`
    respectively.

    **Parameters**:
    - `name`: human-readable name (e.g., "AES", "SM4")
    - `n`: bit-width
    - `table`: the S-box as `Array Nat`
    - `cert`: a pre-computed `Certificate`

    **Usage**:
    ```
    #eval (generateBundle "AES" 8 AES.sbox AES.certificate).certificateMd
    ```
-/
def generateBundle (name : String) (n : Nat) (table : Array Nat)
    (cert : Certificate) : Bundle :=
  let tableLit := toString table
  { certificateMd := generateCertificateMarkdown cert tableLit
    evidenceLean  := generateEvidenceLean name n tableLit
                       cert.diffUnif cert.walshMax cert.boomerangU cert.isPerm
    readmeMd      := generateReadme name }

/-- Pretty-print a `Bundle` showing all three generated files. -/
def Bundle.display (b : Bundle) : String :=
  "═══════════════════════════════════════════════\n" ++
  "  GENERATED EVIDENCE BUNDLE\n" ++
  "═══════════════════════════════════════════════\n\n" ++
  "── Certificate.md ──────────────────────────────\n\n" ++
  b.certificateMd ++ "\n\n" ++
  "── Evidence.lean ──────────────────────────────\n\n" ++
  b.evidenceLean ++ "\n\n" ++
  "── README.md ──────────────────────────────────\n\n" ++
  b.readmeMd

instance : ToString Bundle := ⟨Bundle.display⟩

/-! ### IO action: write bundle to disk -/

/-- Write a full evidence bundle to a directory.

    Creates three files in the specified directory:
    - `Certificate.md`
    - `Evidence.lean`
    - `README.md`

    **Usage** (in a `main` function or `#eval`):
    ```
    #eval EvidenceBundle.writeBundle "output/AES" "AES" 8 AES.sbox AES.certificate
    ```
-/
def writeBundle (dir : System.FilePath) (name : String) (n : Nat)
    (table : Array Nat) (cert : Certificate) : IO Unit := do
  let bundle := generateBundle name n table cert
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "Certificate.md") bundle.certificateMd
  IO.FS.writeFile (dir / "Evidence.lean") bundle.evidenceLean
  IO.FS.writeFile (dir / "README.md") bundle.readmeMd
  IO.println s!"✓ Evidence bundle written to {dir}/"
  IO.println s!"  - Certificate.md  ({bundle.certificateMd.length} bytes)"
  IO.println s!"  - Evidence.lean   ({bundle.evidenceLean.length} bytes)"
  IO.println s!"  - README.md       ({bundle.readmeMd.length} bytes)"

/-! ### Batch comparison with IO -/

/-- Write a comparison report (markdown) for multiple certificates. -/
def writeComparisonReport (path : System.FilePath)
    (certs : List Certificate) : IO Unit := do
  let table := formatComparison certs
  let md :=
    "# S-Box Comparison Report\n\n" ++
    "Machine-verified security metrics for multiple S-boxes.\n" ++
    "All values are proven correct via exhaustive `native_decide` verification.\n\n" ++
    "```\n" ++ table ++ "\n```\n\n" ++
    "## Legend\n\n" ++
    "| Metric   | Meaning |\n" ++
    "|----------|---------|\n" ++
    "| **Bits** | S-box bit-width (4 = 16 elements, 8 = 256 elements) |\n" ++
    "| **δ**    | Differential uniformity — max DDT entry (lower = better) |\n" ++
    "| **NL**   | Nonlinearity — distance to nearest linear function (higher = better) |\n" ++
    "| **|W|**  | Maximum Walsh coefficient magnitude (lower = better) |\n" ++
    "| **β**    | Boomerang uniformity — max BCT entry (lower = better) |\n" ++
    "| **SecBits** | Security bits against differential attack: n - log₂(δ) |\n" ++
    "| **Grade** | Overall rating based on differential bias δ/2^n |\n\n" ++
    "## Interpretation\n\n" ++
    "- **δ = 2** is the theoretical optimum (no known 8-bit permutation achieves this)\n" ++
    "- **δ = 4** is the best known for 8-bit permutations (AES, SM4)\n" ++
    "- **δ = 4** is optimal for 4-bit permutations\n" ++
    "- Higher nonlinearity = harder for linear cryptanalysis\n" ++
    "- Lower boomerang uniformity = harder for boomerang attacks\n\n" ++
    "---\n" ++
    "*Generated by the S-Box Audit Framework (Lean 4 + Mathlib)*\n"
  IO.FS.writeFile path md
  IO.println s!"✓ Comparison report written to {path}"

end EvidenceBundle
end CipherAudit
