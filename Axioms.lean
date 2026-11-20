/- Axiom audit: the kernel prints the axioms each headline result
depends on. The family gate reads this output in the build log.
Expected, for every line: only the standard axioms
(propext, Classical.choice, Quot.sound), and no other. -/

import Cert
import Control

#print axioms Cert.Chain.sound
#print axioms Cert.Chain.join
#print axioms Cert.check.sound
#print axioms Cert.check.honest
#print axioms Cert.check.notcertified
#print axioms Cert.check.chain
#print axioms Cert.certified.sound
#print axioms Control.control
