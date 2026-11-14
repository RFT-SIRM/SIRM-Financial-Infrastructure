import Mathlib
import SIRM.CanonicalRequestEncoding
import SIRM.FinancialTransactionEnvelope

/-!
# Linking the Canonical Encoding to the Envelope Request

Maps the polymorphic `FinancialTransactionRequest` of the envelope layer into
the concrete bounded record `FtxRequest` of `SIRM.CanonicalRequestEncoding`,
using caller-supplied index maps for principals, holders and assets. Proves
that, when those maps are injective and the two compared images are in range,
distinct envelope requests with the same request ID have distinct canonical
encodings.

The index maps are assumptions, not constructed here: choosing the real
principal/holder/asset numbering (for example the position in a finite
registry) and proving the range bounds for it is a separate obligation.
-/

namespace SIRM

section Link

variable {Principal Holder Asset : Type}

/-- Map an envelope operation to the concrete layout operation. -/
def FinancialOperation.toFtxOp (hi : Holder → Nat) (ai : Asset → Nat) :
    FinancialOperation Holder Asset → FtxOp
  | .transfer s d a m => .transfer (hi s) (hi d) (ai a) m
  | .issue i r a m => .issue (hi i) (hi r) (ai a) m
  | .burn h a m => .burn (hi h) (ai a) m

/-- Map an envelope request (with its separately supplied ID) to the layout record. -/
def FinancialTransactionRequest.toFtx (pi : Principal → Nat) (hi : Holder → Nat)
    (ai : Asset → Nat) (rid : Nat)
    (r : FinancialTransactionRequest Principal Holder Asset) : FtxRequest :=
  { requestId := rid
    principal := pi r.principal
    nonce := r.nonce
    op := r.operation.toFtxOp hi ai }

theorem toFtxOp_injective {hi : Holder → Nat} {ai : Asset → Nat}
    (hh : Function.Injective hi) (ha : Function.Injective ai) :
    Function.Injective (FinancialOperation.toFtxOp (Holder := Holder) (Asset := Asset) hi ai) := by
  intro x y h
  cases x <;> cases y <;>
    simp_all [FinancialOperation.toFtxOp, hh.eq_iff, ha.eq_iff]

theorem toFtx_injective {pi : Principal → Nat} {hi : Holder → Nat} {ai : Asset → Nat}
    (hp : Function.Injective pi) (hh : Function.Injective hi)
    (ha : Function.Injective ai) (rid : Nat) :
    Function.Injective
      (FinancialTransactionRequest.toFtx (Principal := Principal) (Holder := Holder)
        (Asset := Asset) pi hi ai rid) := by
  intro r s h
  have hpp := congrArg FtxRequest.principal h
  have hnn := congrArg FtxRequest.nonce h
  have hop := congrArg FtxRequest.op h
  obtain ⟨p, n, op⟩ := r
  obtain ⟨p', n', op'⟩ := s
  simp only [FinancialTransactionRequest.toFtx] at hpp hnn hop
  have e1 := hp hpp
  have e2 := toFtxOp_injective hh ha hop
  subst e1
  subst hnn
  subst e2
  rfl

/-- Two envelope requests with the same request ID and the same canonical encoding are
equal, provided the index maps are injective and both images are in range (`Valid`).
Range validity is required only for the two compared requests, not for all requests. -/
theorem encodeRequest_toFtx_injective
    {pi : Principal → Nat} {hi : Holder → Nat} {ai : Asset → Nat}
    (hp : Function.Injective pi) (hh : Function.Injective hi)
    (ha : Function.Injective ai) (rid : Nat)
    {r s : FinancialTransactionRequest Principal Holder Asset}
    (hr : (r.toFtx pi hi ai rid).Valid) (hs : (s.toFtx pi hi ai rid).Valid)
    (h : encodeRequest (r.toFtx pi hi ai rid) = encodeRequest (s.toFtx pi hi ai rid)) :
    r = s :=
  toFtx_injective hp hh ha rid (encodeRequest_injective hr hs h)

end Link

end SIRM
