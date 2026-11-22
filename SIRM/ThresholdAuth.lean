import SIRM.SignatureSuite

/-!
# Threshold Authorization (abstract model)

A threshold policy lists `n` registered keys and a threshold `k`. An authorization carries a
list of `(index, signature)` pairs over the same message. It is accepted when at least `k`
**distinct** key indices have a signature that the abstract verifier accepts for the key
registered at that index, under a suite that the node policy permits.

No aggregation or threshold-signature scheme is assumed: this is a plain list of independent
signatures, which is what the post-quantum proposal specifies. The verifier is an arbitrary
parameter; nothing here proves unforgeability of any real scheme.
-/

namespace SIRM

section Threshold

variable {PublicKey Message Signature : Type}

/-- A threshold policy: the registered keys and the number `k` of distinct approvals needed. -/
structure ThresholdPolicy (PublicKey : Type) where
  keys : List (KeyRecord PublicKey)
  k : Nat

/-- Index `i` counts if its registered key has a permitted suite and some supplied signature
labelled `i` verifies for it. -/
def validIdx (M : SignatureModel PublicKey Message Signature) (P : SuitePolicy)
    (tp : ThresholdPolicy PublicKey) (msg : Message) (sigs : List (Nat × Signature))
    (i : Nat) : Bool :=
  match tp.keys[i]? with
  | none => false
  | some r => P.permits r.suite && sigs.any (fun js => js.1 == i && M.verify r.suite r.key msg js.2)

/-- The counted indices: each index at most once, whatever the signature list contains. -/
def validIndices (M : SignatureModel PublicKey Message Signature) (P : SuitePolicy)
    (tp : ThresholdPolicy PublicKey) (msg : Message) (sigs : List (Nat × Signature)) :
    List Nat :=
  (List.range tp.keys.length).filter (validIdx M P tp msg sigs)

/-- Accept when `k` is positive and at least `k` distinct indices count. -/
def thresholdAccepts (M : SignatureModel PublicKey Message Signature) (P : SuitePolicy)
    (tp : ThresholdPolicy PublicKey) (msg : Message) (sigs : List (Nat × Signature)) : Bool :=
  decide (0 < tp.k) && decide (tp.k ≤ (validIndices M P tp msg sigs).length)

/-- An empty threshold never accepts: zero approvals cannot authorize. -/
theorem zero_threshold_rejected (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) (tp : ThresholdPolicy PublicKey) (msg : Message)
    (sigs : List (Nat × Signature)) (h : tp.k = 0) :
    thresholdAccepts M P tp msg sigs = false := by
  simp [thresholdAccepts, h]

/-- Acceptance implies `k` distinct indices, each with a signature in the list that the verifier
accepts for the key registered at that index, under a suite that the policy permits. -/
theorem accepts_implies_k_distinct (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) (tp : ThresholdPolicy PublicKey) (msg : Message)
    (sigs : List (Nat × Signature)) (h : thresholdAccepts M P tp msg sigs = true) :
    0 < tp.k ∧ ∃ l : List Nat, l.Nodup ∧ tp.k ≤ l.length ∧
      ∀ i ∈ l, ∃ r sg, tp.keys[i]? = some r ∧ P.permits r.suite = true ∧ (i, sg) ∈ sigs ∧
        M.verify r.suite r.key msg sg = true := by
  simp only [thresholdAccepts, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hk, hl⟩ := h
  refine ⟨hk, validIndices M P tp msg sigs, ?_, hl, ?_⟩
  · exact (List.nodup_range).filter _
  · intro i hi
    simp only [validIndices, List.mem_filter] at hi
    have hv := hi.2
    simp only [validIdx] at hv
    cases hr : tp.keys[i]? with
    | none => simp [hr] at hv
    | some r =>
      rw [hr] at hv
      simp only [Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at hv
      obtain ⟨hp, ⟨i', sg⟩, hm, hi', hver⟩ := hv
      simp only at hi'
      subst hi'
      exact ⟨r, sg, rfl, hp, hm, hver⟩

/-- The policy lists pairwise different public keys: two indices never share a key. The counting above
is by index, so this is a requirement on the registered policy, not something the acceptance function
checks; without it one key registered twice counts twice (see `duplicate_key_counts_twice`). -/
def KeysDistinct (tp : ThresholdPolicy PublicKey) : Prop :=
  ∀ (i j : Nat) (r r' : KeyRecord PublicKey), tp.keys[i]? = some r → tp.keys[j]? = some r' →
    r.key = r'.key → i = j

/-- On a policy with pairwise different keys, acceptance implies `k` verified signatures from `k`
different registered public keys: the counted indices are distinct and no two of them share a key. -/
theorem accepts_implies_k_distinct_signers (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) (tp : ThresholdPolicy PublicKey) (msg : Message)
    (sigs : List (Nat × Signature)) (hd : KeysDistinct tp)
    (h : thresholdAccepts M P tp msg sigs = true) :
    0 < tp.k ∧ ∃ l : List Nat, l.Nodup ∧ tp.k ≤ l.length ∧
      (∀ i ∈ l, ∃ r sg, tp.keys[i]? = some r ∧ P.permits r.suite = true ∧ (i, sg) ∈ sigs ∧
        M.verify r.suite r.key msg sg = true) ∧
      ∀ i ∈ l, ∀ j ∈ l, ∀ (r r' : KeyRecord PublicKey), tp.keys[i]? = some r → tp.keys[j]? = some r' →
        r.key = r'.key → i = j := by
  obtain ⟨hk, l, hn, hl, hv⟩ := accepts_implies_k_distinct M P tp msg sigs h
  exact ⟨hk, l, hn, hl, hv, fun i _ j _ r r' hr hr' he => hd i j r r' hr hr' he⟩

/-- With no verifying signature at all, nothing is accepted. -/
theorem no_verifying_signature_rejected (M : SignatureModel PublicKey Message Signature)
    (P : SuitePolicy) (tp : ThresholdPolicy PublicKey) (msg : Message)
    (sigs : List (Nat × Signature)) (hk : 0 < tp.k)
    (h : ∀ i, validIdx M P tp msg sigs i = false) :
    thresholdAccepts M P tp msg sigs = false := by
  have hnil : validIndices M P tp msg sigs = [] := by
    simp [validIndices, h]
  simp [thresholdAccepts, hnil, Nat.pos_iff_ne_zero.mp hk]

/-- Repeating a signature does not add approvals: duplicates never count twice. -/
theorem validIdx_dup (M : SignatureModel PublicKey Message Signature) (P : SuitePolicy)
    (tp : ThresholdPolicy PublicKey) (msg : Message) (sigs : List (Nat × Signature))
    (i : Nat) :
    validIdx M P tp msg (sigs ++ sigs) i = validIdx M P tp msg sigs i := by
  simp [validIdx, List.any_append]

/-- Hence the accepted decision is unchanged by duplicating the whole signature list. -/
theorem accepts_dup (M : SignatureModel PublicKey Message Signature) (P : SuitePolicy)
    (tp : ThresholdPolicy PublicKey) (msg : Message) (sigs : List (Nat × Signature)) :
    thresholdAccepts M P tp msg (sigs ++ sigs) = thresholdAccepts M P tp msg sigs := by
  have hf : validIdx M P tp msg (sigs ++ sigs) = validIdx M P tp msg sigs :=
    funext (validIdx_dup M P tp msg sigs)
  unfold thresholdAccepts validIndices
  rw [hf]

/-- A lower threshold is easier: acceptance at `k` implies acceptance at any smaller positive
threshold over the same keys and signatures. -/
theorem accepts_mono (M : SignatureModel PublicKey Message Signature) (P : SuitePolicy)
    (keys : List (KeyRecord PublicKey)) (k k' : Nat) (msg : Message)
    (sigs : List (Nat × Signature)) (hk' : 0 < k') (hle : k' ≤ k)
    (h : thresholdAccepts M P ⟨keys, k⟩ msg sigs = true) :
    thresholdAccepts M P ⟨keys, k'⟩ msg sigs = true := by
  have hv : validIndices M P ⟨keys, k'⟩ msg sigs = validIndices M P ⟨keys, k⟩ msg sigs := rfl
  simp only [thresholdAccepts, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  rw [hv]
  exact ⟨hk', Nat.le_trans hle h.2⟩

end Threshold

/-! ### Concrete regression examples (toy verifier: accepts exactly signature `7`) -/

section Demo

def demoPolicyT : SuitePolicy where
  status := fun s => if s = 2 then .active else .proposed
  allowDeprecated := false

def demoModelT : SignatureModel Nat Nat Nat := ⟨fun _ _ _ s => s == 7⟩

def demoThreshold : ThresholdPolicy Nat :=
  ⟨[⟨2, 10⟩, ⟨2, 11⟩, ⟨2, 12⟩], 2⟩

-- two distinct approvals reach 2-of-3
example : thresholdAccepts demoModelT demoPolicyT demoThreshold 0 [(0, 7), (2, 7)] = true := by
  decide
-- one approval, even repeated, does not
example : thresholdAccepts demoModelT demoPolicyT demoThreshold 0 [(1, 7), (1, 7), (1, 7)] = false := by
  decide
-- a bad signature does not count
example : thresholdAccepts demoModelT demoPolicyT demoThreshold 0 [(0, 7), (2, 8)] = false := by
  decide
/-- Without `KeysDistinct` one key registered at two indices counts twice. -/
theorem duplicate_key_counts_twice :
    thresholdAccepts demoModelT demoPolicyT ⟨[⟨2, 10⟩, ⟨2, 10⟩, ⟨2, 12⟩], 2⟩ 0 [(0, 7), (1, 7)] = true := by
  decide

-- an index outside the policy does not count
example : thresholdAccepts demoModelT demoPolicyT demoThreshold 0 [(0, 7), (5, 7)] = false := by
  decide

end Demo

end SIRM
