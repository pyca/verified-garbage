module

public import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PostMono

/-!
# A longer read-only first array, on x86-64

A function proven against `sig.contract A pre post …`, whose first
parameter is a read-only array of `n` elements, is proven against the same
contract with that array `n' ≥ n` elements long and a precondition `pre'`
that implies `pre` (`Verified.widenFirstArray`): it reads the first `n`
elements only, which the longer array begins with. The code runs as it does
with the array's region narrowed to its first `n` elements
(`RegionModel.verified_narrowTo`), from a state that permits less: the same
registers, memory and other regions.

AES-GCM's functions that read the key context of `vg_aes_gcm_init` (256
bytes) are proven so against the contracts of the functions that take a
1024-byte key context, which begins with it.
-/

@[expose] public section

namespace VG.X86_64

/-- The signature `params` with a read-only first array of `n` elements of
`e`, named `name`. -/
abbrev firstArraySig (name : String) (e : Elem) (n : Nat) (rest : List (String × Param))
    (ret : Option IntTy) : Sig :=
  { params := (name, .array false e n) :: rest, ret := ret }

/-- The words of `firstArraySig` do not depend on the array's length. -/
theorem firstArraySig_words (name : String) (e : Elem) (n n' : Nat) (rest : List (String × Param))
    (ret : Option IntTy) (pb : Nat) :
    (firstArraySig name e n' rest ret).words pb = (firstArraySig name e n rest ret).words pb := rfl

/-- The regions `rs`, with the first narrowed to at most `len` bytes. -/
def narrowHead (len : Nat) (rs : List Region) : List Region :=
  match rs with
  | [] => []
  | r :: rs => ⟨r.base, min len r.len⟩ :: rs

/-- Every list of regions extends itself. -/
theorem forall₂_prefix_refl (rs : List Region) : List.Forall₂ Region.Prefix rs rs := by
  induction rs with
  | nil => exact .nil
  | cons r rs ih => exact .cons ⟨rfl, Nat.le_refl _⟩ ih

/-- The regions extend themselves with the first narrowed. -/
theorem narrowHead_append_prefix (len : Nat) (rs ws : List Region) :
    List.Forall₂ Region.Prefix (narrowHead len rs ++ ws) (rs ++ ws) := by
  cases rs with
  | nil => exact forall₂_prefix_refl _
  | cons r rs => exact .cons ⟨rfl, Nat.min_le_right ..⟩ (forall₂_prefix_refl _)

/-- The arguments `abi` reads do not depend on the regions a state permits. -/
theorem abi_args_withRegions {ws : List Nat} {vals : State → List (BitVec 64)}
    (h : abi.args ws = some vals) (s : State) (rd wr : List Region) :
    vals (s.withRegions rd wr) = vals s := by
  simp only [abi] at h
  split at h <;> cases h <;> rfl

/-- `abi` reads an argument for each of at least one word. -/
theorem abi_args_cons {ws : List Nat} {vals : State → List (BitVec 64)}
    (h : abi.args ws = some vals) (hws : ws ≠ []) (s : State) :
    ∃ p vs, vals s = p :: vs := by
  simp only [abi] at h
  split at h <;> cases h
  · cases ws with
    | nil => exact absurd rfl hws
    | cons w ws => exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

/-- The descriptors of `Sig.descs` do not depend on an array's length. -/
theorem descs_array {name : String} {rest : List (String × Param)} (e : Elem) (n n' : Nat)
    (vs : List (BitVec 64)) :
    Sig.descs 64 ((name, .array false e n') :: rest) vs =
      Sig.descs 64 ((name, .array false e n) :: rest) vs := by
  cases vs <;> rfl

/-- Moving a proof to a longer read-only first array and a stronger
precondition, all else the same. -/
theorem Verified.widenFirstArray {c : Prog isa} {name : String} {e : Elem} {n n' : Nat}
    (hn : n ≤ n') {rest : List (String × Param)} {ret : Option IntTy}
    {pre : Curry ((firstArraySig name e n rest ret).words 64) (Mem → Prop)}
    {pre' : Curry ((firstArraySig name e n' rest ret).words 64) (Mem → Prop)}
    {post : (firstArraySig name e n rest ret).Post 64} {wa : Bool} {stack : Nat}
    {leak : Option (Curry ((firstArraySig name e n rest ret).words 64) (Mem → List Nat))}
    (h : Verified target c ((firstArraySig name e n rest ret).contract abi pre post wa stack leak))
    (hp : Curry.Forall₂ (fun p q => ∀ m, p m → q m) _ pre' pre)
    (hsat : ∃ s, ((firstArraySig name e n' rest ret).contract abi pre' post wa stack leak).pre s) :
    Verified target c ((firstArraySig name e n' rest ret).contract abi pre' post wa stack leak) := by
  refine regionModel.verified_narrowTo (T := target) (fun _ _ _ _ h => h) h
    (fun s => narrowHead (n * e.size) s.rd) (fun s => s.wr) ?_ ?_ (fun _ _ => Covers.refl _)
    ?_ ?_ hsat
  · intro s hs
    dsimp only [Sig.contract] at hs ⊢
    split at hs
    · exact hs.elim
    rename_i vals hvals
    split
    · rename_i h'; exact absurd (hvals.symm.trans h') nofun
    rename_i vals' hvals'
    obtain rfl : vals' = vals := Option.some.inj (hvals'.symm.trans hvals)
    have hw := abi_args_withRegions hvals s (narrowHead (n * e.size) s.rd) s.wr
    obtain ⟨p, vs, hv⟩ := abi_args_cons hvals (by simp [Sig.words, Param.words]) s
    have hW : List.map (fun x => ArgWord.bits abi.ptrBits x)
        ((firstArraySig name e n rest ret).words abi.ptrBits) =
        List.map (fun x => ArgWord.bits abi.ptrBits x)
        ((firstArraySig name e n' rest ret).words abi.ptrBits) := rfl
    simp only [regionModel, hw] at hs ⊢
    rw [hv] at hs ⊢
    simp only [Sig.bufs, Sig.lists, List.cons_append, List.filter_cons] at hs ⊢
    rw [hW]
    generalize List.map (fun x => ArgWord.bits abi.ptrBits x)
        ((firstArraySig name e n' rest ret).words abi.ptrBits) = W at hs ⊢
    have hm : abi.mem (s.withRegions (narrowHead (n * e.size) s.rd) s.wr) = abi.mem s := rfl
    have ha : abi.argArea W (s.withRegions (narrowHead (n * e.size) s.rd) s.wr) =
      abi.argArea W s := rfl
    have hr : abi.reserved stack (s.withRegions (narrowHead (n * e.size) s.rd) s.wr) =
      abi.reserved stack s := rfl
    simp only [hm, ha, hr, Bool.not_false, Bool.false_eq_true, ↓reduceIte, List.map_cons] at hs ⊢
    generalize Sig.bufs rest vs ++ List.map (fun r => (r, false))
      (Sig.lists abi.ptrBits (abi.mem s) rest vs) = B at hs ⊢
    obtain ⟨hwf, hrd, hwr, hpw, hres, hb, hpre⟩ := hs
    have hsub : Region.Sub ⟨p, n * e.size⟩ ⟨p, n' * e.size⟩ :=
      Region.sub_prefix (Nat.mul_le_mul_right _ hn)
    refine ⟨hwf, ?_, hwr, ?_, ?_, ?_, ?_⟩
    · change narrowHead (n * e.size) (abi.rd s) = _
      rw [hrd, narrowHead, Nat.min_eq_left (Nat.mul_le_mul_right _ hn)]
    · rw [List.pairwise_cons] at hpw ⊢
      exact ⟨fun b hb hd => (hpw.1 b hb hd).sub_left hsub, hpw.2⟩
    · intro r hr' a ha'
      rcases List.mem_cons.mp ha' with rfl | ha'
      · exact (hres r hr' _ (List.mem_cons_self ..)).sub_right hsub
      · exact hres r hr' a (List.mem_cons_of_mem _ ha')
    · intro a ha'
      rcases List.mem_cons.mp ha' with rfl | ha'
      · have := hb _ (List.mem_cons_self ..)
        have := Nat.mul_le_mul_right e.size hn
        dsimp only at *; omega
      · exact hb a (List.mem_cons_of_mem _ ha')
    · exact hp.apply _ _ hpre
  · exact fun s _ _ _ => InRegions.of_prefix (narrowHead_append_prefix _ _ _)
  · intro s s' _ h
    dsimp only [Sig.contract] at h ⊢
    split at h
    · exact h.elim
    rename_i vals hvals
    split
    · rename_i h'; exact absurd (hvals.symm.trans h') nofun
    rename_i vals' hvals'
    obtain rfl : vals' = vals := Option.some.inj (hvals'.symm.trans hvals)
    simp only [regionModel, abi_args_withRegions hvals] at h
    exact h
  · intro s₁ s₂ _ _ h
    dsimp only [Sig.contract] at h ⊢
    split at h
    · exact h.elim
    rename_i vals hvals
    split
    · rename_i h'; exact absurd (hvals.symm.trans h') nofun
    rename_i vals' hvals'
    obtain rfl : vals' = vals := Option.some.inj (hvals'.symm.trans hvals)
    have hm (s : State) : abi.mem (s.withRegions (narrowHead (n * e.size) s.rd) s.wr) = abi.mem s :=
      rfl
    have hq : abi.pub (s₁.withRegions (narrowHead (n * e.size) s₁.rd) s₁.wr)
      (s₂.withRegions (narrowHead (n * e.size) s₂.rd) s₂.wr) = abi.pub s₁ s₂ := rfl
    simp only [regionModel, abi_args_withRegions hvals, hm, hq]
    refine ⟨?_, h.2.1, ?_⟩
    · cases leak
      · exact h.1
      · exact h.1
    · exact (descs_array (name := name) (rest := rest) e n n' (vals' s₁)) ▸ h.2.2

end VG.X86_64
