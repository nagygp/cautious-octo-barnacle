# Machine-Checked S-Box Security Certificates — Public Reports

> A small, free, reproducible portfolio of formally verified S-box security
> audits, produced with the `AuditSBox` toolkit (Lean 4 + Mathlib).

## What this is (the 60-second version)

Most published S-box security numbers — "AES has differential uniformity 4",
"its nonlinearity is 112" — are *claims*. They are correct, but to trust them
you either re-derive them yourself or take someone's word.

This project turns those claims into **theorems**. For each S-box the toolkit
computes the full differential, linear, and boomerang tables *inside a
kernel-checked proof* (`native_decide`). A third party re-runs `lake build`
and obtains exactly the same guarantee, with **zero trust in the auditor**.

Each report in this folder pairs:

- a plain-English security summary (what the numbers mean and how strong the
  S-box is), and
- a pointer to the machine-verifiable evidence (`outputs-example/<CIPHER>/`),
  which anyone can re-check.

## The reports

| Cipher | Width | δ | NL | \|W\| | β | Verdict | Report |
|---|---|---|---|---|---|---|---|
| **AES** (Rijndael) | 8-bit | 4 | 112 | 32 | 6 | Best-in-class 8-bit S-box | [AES](./AES-audit-report.md) |
| **ASCON** | 5-bit | 8 | 8 | 16 | 16 | Sound lightweight χ-style S-box | [ASCON](./ASCON-audit-report.md) |
| **GIFT** | 4-bit | 6 | 4 | 8 | 16 | Ultra-lightweight, weak in isolation | [GIFT](./GIFT-audit-report.md) |

Legend: **δ** differential uniformity (max DDT entry, lower is better) ·
**NL** nonlinearity (higher is better) · **\|W\|** max Walsh magnitude (lower is
better) · **β** boomerang uniformity (lower is better).

All numbers in these reports are *reproduced from public specifications and
agree with the published literature* — the contribution here is not new
numbers, it is that each number is a re-checkable machine proof.

## How to verify any report yourself (≈ 2 minutes of typing, then a build)

1. Install Lean 4 (`elan`):
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```
2. From the project root, build:
   ```bash
   lake build
   ```
3. If `lake build` succeeds, **every** security claim in every report is proven.
   If it fails, a claim is wrong.

Each `outputs-example/<CIPHER>/` folder also ships a self-contained
`Evidence.lean` and a `README.md` with the same instructions, so a single
cipher's certificate can be checked on its own.

## What `native_decide` actually does

For an n-bit S-box the DDT (differential), Walsh (linear), and BCT (boomerang)
tables are *finite*. The proof method:

1. defines a Boolean check (e.g. "is every DDT entry ≤ δ?"),
2. compiles it to native code,
3. runs it **exhaustively** over all inputs (e.g. all 256 × 256 input pairs for
   an 8-bit S-box), and
4. has the Lean kernel verify the result.

This is complete enumeration — no sampling, no heuristics. The only extra trust
assumption beyond Lean's logic is the compiled-evaluation axioms
(`Lean.ofReduceBool` / `Lean.trustCompiler`); everything else is `propext` /
`Classical.choice` / `Quot.sound`.

## Scope and honest limitations

- These certificates audit the **S-box in isolation** (its DDT/Walsh/BCT
  profile). They do **not** audit a full cipher, an implementation, key
  schedule, side channels, or protocol usage. A strong S-box is necessary, not
  sufficient, for a secure cipher.
- The metrics certified (δ, NL, \|W\|, β) are standard and cheap to compute with
  other tools; the differentiator here is the *re-checkable proof*, not the
  values.
- For small (4–8 bit) S-boxes the values are long-settled public knowledge. The
  highest-leverage use of this capability is where brute force is impossible —
  e.g. power-map S-boxes over large prime fields (Poseidon-style, ZK circuits),
  where a *symbolic* proof is the only option. That extension lives under
  `AuditSBox/PrimeField/`.

---
*Produced with the `AuditSBox` toolkit. See [`../AUDIT_SBOX.md`](../AUDIT_SBOX.md)
for a full audit of the toolkit itself, and [`../README.md`](../README.md) for
the repository overview.*
