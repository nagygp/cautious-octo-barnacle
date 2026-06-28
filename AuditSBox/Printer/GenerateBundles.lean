import AuditSBox.Printer.EvidenceBundle
import AuditSBox.Examples.AES
import AuditSBox.Examples.GIFT
import AuditSBox.Examples.ASCON
import AuditSBox.Examples.SM4
import AuditSBox.Examples.SKINNY
import AuditSBox.Examples.SKINNY8
import AuditSBox.Examples.PRESENT
import AuditSBox.Examples.Serpent
import AuditSBox.Examples.Camellia
import AuditSBox.Examples.Midori
import AuditSBox.Examples.PRINCE
import AuditSBox.Examples.KeccakChi
import AuditSBox.Examples.ToySbox

/-!
# Evidence Bundle & Comparison Report Generator

This file demonstrates the audit loop and evidence bundle generation.
Run `lake exec generate_bundles` (if wired as an executable) or
use `#eval` in the editor to generate deliverables.

## Quick demo

To generate a bundle for a specific S-box, uncomment one of the
`#eval` lines below. Each writes three files (Certificate.md,
Evidence.lean, README.md) to the specified output directory.

To print the comparison table for all audited S-boxes, uncomment
the `#eval printComparison` line.
-/

open CipherAudit EvidenceBundle

/-! ### All certificates in one list -/

/-- Master list of all audited S-box certificates. -/
def allCertificates : List CipherAudit.Certificate := [
  AES.certificate,
  SM4.certificate,
  Camellia.S1.certificate,
  Camellia.S2.certificate,
  Camellia.S3.certificate,
  Camellia.S4.certificate,
  GIFT.certificate,
  ASCON.certificate,
  SKINNY.certificate,
  SKINNY8.certificate,
  PRESENT.certificate,
  Serpent.S0.certificate,
  Serpent.S1.certificate,
  Serpent.S2.certificate,
  Serpent.S3.certificate,
  Serpent.S4.certificate,
  Serpent.S5.certificate,
  Serpent.S6.certificate,
  Serpent.S7.certificate,
  Midori.Sb0.certificate,
  Midori.Sb1.certificate,
  PRINCE.certificate,
  KeccakChi.certificate,
  ToySbox.certificate
]

/-! ### Print comparison table -/

-- Uncomment to print the full comparison table:
-- #eval printComparison allCertificates

/-! ### Generate evidence bundles -/

-- Uncomment any of these to generate a bundle to disk:
-- #eval writeBundle "output/AES" "AES" 8 AES.sbox AES.certificate
-- #eval writeBundle "output/SM4" "SM4" 8 SM4.sbox SM4.certificate
-- #eval writeBundle "output/Camellia-S1" "Camellia-S1" 8 Camellia.sbox1 Camellia.S1.certificate
-- #eval writeBundle "output/GIFT" "GIFT" 4 GIFT.sbox GIFT.certificate
-- #eval writeBundle "output/SKINNY" "SKINNY" 4 SKINNY.sbox SKINNY.certificate
-- #eval writeBundle "output/PRESENT" "PRESENT" 4 PRESENT.sbox PRESENT.certificate

/-! ### Generate comparison report -/

-- Uncomment to write comparison report:
-- #eval writeComparisonReport "output/ComparisonReport.md" allCertificates
