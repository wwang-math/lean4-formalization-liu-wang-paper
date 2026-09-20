/-!
# Verification status
-/

namespace LiuWangVerification

inductive VerificationStatus where
  | verified
  | assumptionTracked
  | openBridge
deriving DecidableEq, Repr

end LiuWangVerification
