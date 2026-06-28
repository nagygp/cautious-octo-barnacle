import AuditSBox.Printer.GenerateBundles

/-!
# Output generator (executable)

Regenerates the sample deliverables under `outputs-example/`.

Run with:

```
lake exe generate
```

It writes a full comparison report plus a few representative single-S-box
evidence bundles.  The formatting is pure; the underlying security numbers
come from the certificates in `Examples/`, each of which is itself verified
by `native_decide`.
-/

open CipherAudit EvidenceBundle

def main : IO Unit := do
  let outDir : System.FilePath := "outputs-example"
  IO.FS.createDirAll outDir
  -- Full comparison report across every audited S-box.
  writeComparisonReport (outDir / "ComparisonReport.md") allCertificates
  -- Plain-text comparison table (as printed to the console).
  IO.FS.writeFile (outDir / "ComparisonTable.txt") (formatComparison allCertificates)
  -- A few representative single-S-box evidence bundles.
  writeBundle (outDir / "AES") "AES" 8 AES.sbox AES.certificate
  writeBundle (outDir / "GIFT") "GIFT" 4 GIFT.sbox GIFT.certificate
  writeBundle (outDir / "ASCON") "ASCON" 5 ASCON.sbox ASCON.certificate
  IO.println "✓ outputs-example/ regenerated"
