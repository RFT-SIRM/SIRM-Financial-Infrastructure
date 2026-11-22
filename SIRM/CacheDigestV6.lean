import SIRM.StateCommitmentV6

/-!
# The cache digest of state commitment v6 (checked by SIRM)

    cache digest = H("SIRM/CAC/v6\0" | n u32 | entry_1 | ... | entry_n)
    entry        = request encoding v2 (request id included) | stored outcome (11 bytes)

The entries are written one after the other with no separator. This file proves that this is
unambiguous: an entry carries its own length (the operation tag at byte 44 fixes the width of the
request, and the stored outcome has 11 bytes), so the concatenation of valid entries determines the
list of entries, and with a collision-free hash (a hypothesis, as in `SIRM.StateCommitmentV6`) the
digest determines the list of cached requests and outcomes (`cacheDigest_binds`).

Not modelled: that the machine sorts its entries by request id and builds this list from its state, the
state root that contains the digest (see `SIRM.StateCommitmentV6.root_binds`), SHA-256.
-/

namespace SIRM
namespace CacheDigestV6

open RequestEncodingV2 StateCommitmentV6

/-- "SIRM/CAC/v6\0" -/
def cacDomain : List Nat := [83, 73, 82, 77, 47, 67, 65, 67, 47, 118, 54, 0]

theorem cacDomain_length : cacDomain.length = 12 := by decide

/-- Length of the entry that starts a byte string, read from the operation tag at offset 44. -/
def entryLen (l : List Nat) : Nat :=
  match l[44]? with
  | some t =>
    match widths t with
    | some ws => 45 + ws.sum + 11
    | none => 0
  | none => 0

theorem encFields_length : ∀ {ws vs : List Nat}, Fits ws vs → (encFields ws vs).length = ws.sum
  | [], [], _ => by simp [encFields]
  | w :: ws, v :: vs, h => by
      simp only [encFields, List.length_append, be_length, List.sum_cons]
      rw [encFields_length h.2]
  | [], _ :: _, h => absurd h (by simp [Fits])
  | _ :: _, [], h => absurd h (by simp [Fits])

theorem encode_length {r : Req} {ws : List Nat} (hv : r.Valid) (hw : widths r.tag = some ws) :
    (encode r).length = 45 + ws.sum := by
  obtain ⟨_, _, _, _, ws', hw', hf, _⟩ := hv
  rw [hw] at hw'
  cases hw'
  unfold encode
  rw [hw]
  simp only [List.length_append, be_length, List.length_singleton]
  rw [encFields_length hf]

theorem encode_tag_at {r : Req} (rest : List Nat) :
    (encode r ++ rest)[44]? = some r.tag := by
  have h : encode r ++ rest =
      (be 32 r.rid ++ be 4 r.principal ++ be 8 r.nonce) ++
        (r.tag :: ((match widths r.tag with
                    | some ws => encFields ws r.fields
                    | none => []) ++ rest)) := by
    unfold encode; simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl
  rw [h, List.getElem?_append_right (by simp [be_length])]
  simp [be_length]

/-- A valid cache entry carries its own length. -/
def SD (e : List Nat) : Prop := 0 < e.length ∧ ∀ rest, entryLen (e ++ rest) = e.length

theorem cacheEntry_sd {r : Req} {o : Out} (hr : r.Valid) : SD (cacheEntry r o) := by
  obtain ⟨ws, hw, _, _⟩ := hr.2.2.2.2
  have hl := encode_length hr hw
  have hlen : (cacheEntry r o).length = 45 + ws.sum + 11 := by
    unfold cacheEntry; rw [List.length_append, hl, outBytes_length]
  refine ⟨by omega, fun rest => ?_⟩
  have : cacheEntry r o ++ rest = encode r ++ (outBytes o ++ rest) := by
    unfold cacheEntry; simp [List.append_assoc]
  rw [this]
  unfold entryLen
  rw [encode_tag_at]
  simp only [hw]
  rw [hlen]

/-- The hashed payload of the cache digest. -/
def cachePayload (es : List (Req × Out)) : List Nat :=
  cacDomain ++ (be 4 es.length ++ (es.map (fun p => cacheEntry p.1 p.2)).flatten)

def PValid (p : Req × Out) : Prop := p.1.Valid ∧ p.2.Valid

/-- The concatenation of valid entries determines the entries. -/
theorem flatten_injective : ∀ (es fs : List (Req × Out)), (∀ p ∈ es, PValid p) → (∀ p ∈ fs, PValid p) →
    (es.map (fun p => cacheEntry p.1 p.2)).flatten = (fs.map (fun p => cacheEntry p.1 p.2)).flatten →
    es = fs
  | [], [], _, _, _ => rfl
  | [], q :: fs, _, hf, h => by
      have hq := (cacheEntry_sd (o := q.2) (hf q (by simp)).1).1
      simp only [List.map_nil, List.flatten_nil, List.map_cons, List.flatten_cons] at h
      have := congrArg List.length h
      simp only [List.length_nil, List.length_append] at this
      omega
  | p :: es, [], hes, _, h => by
      have hp := (cacheEntry_sd (o := p.2) (hes p (by simp)).1).1
      simp only [List.map_nil, List.flatten_nil, List.map_cons, List.flatten_cons] at h
      have := congrArg List.length h
      simp only [List.length_nil, List.length_append] at this
      omega
  | p :: es, q :: fs, hes, hf, h => by
      have hp := hes p (by simp)
      have hq := hf q (by simp)
      simp only [List.map_cons, List.flatten_cons] at h
      have e1 := (cacheEntry_sd (o := p.2) hp.1).2 ((es.map (fun p => cacheEntry p.1 p.2)).flatten)
      have e2 := (cacheEntry_sd (o := q.2) hq.1).2 ((fs.map (fun p => cacheEntry p.1 p.2)).flatten)
      rw [h] at e1
      have hlen : (cacheEntry p.1 p.2).length = (cacheEntry q.1 q.2).length := by rw [← e1, e2]
      obtain ⟨he, hr⟩ := List.append_inj h hlen
      obtain ⟨e3, e4⟩ := cacheEntry_injective hp.1 hq.1 hp.2 hq.2 he
      have ih := flatten_injective es fs (fun x hx => hes x (by simp [hx]))
        (fun x hx => hf x (by simp [hx])) hr
      have : p = q := Prod.ext e3 e4
      rw [this, ih]

/-- Under a collision-free hash the cache digest determines the list of cached requests and outcomes. -/
theorem cacheDigest_binds {H : List Nat → List Nat} (hH : CollisionFree H)
    {es fs : List (Req × Out)} (hes : ∀ p ∈ es, PValid p) (hfs : ∀ p ∈ fs, PValid p)
    (h : H (cachePayload es) = H (cachePayload fs)) : es = fs := by
  have h1 := hH _ _ h
  unfold cachePayload at h1
  obtain ⟨_, h2⟩ := List.append_inj h1 (by rw [cacDomain_length])
  obtain ⟨_, h3⟩ := List.append_inj h2 (by rw [be_length, be_length])
  exact flatten_injective es fs hes hfs h3

end CacheDigestV6
end SIRM
