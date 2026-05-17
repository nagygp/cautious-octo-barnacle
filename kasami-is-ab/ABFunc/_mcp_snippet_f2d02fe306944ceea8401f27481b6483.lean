import Detect.Equivalence
import Detect.Invariants

-- Key finding: x¹⁵ = x^{(2+1)(4+1)} is APN on GF(2⁷) but is NOT
-- a Gold/Kasami/Welch exponent — it's genuinely a "Double-Gold" (AB6)
#eval classifyExponent 7 15  -- should be "Unknown/New"

-- All APN power maps on GF(2⁷), classified (orbit-reduced)
#eval canonicalAPNScan 7

-- Frobenius orbit of 15 on GF(2⁷)
#eval frobeniusOrbit 7 15

-- Is 15 Frobenius-equivalent to any known family?
#eval isGoldExp 7 15     -- false
#eval isKasamiExp 7 15   -- false
#eval isWelchExp 7 15    -- false
#eval isInverseExp 7 15  -- false
