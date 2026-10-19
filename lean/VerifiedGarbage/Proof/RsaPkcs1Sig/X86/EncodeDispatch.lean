module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.EncodeBytes

/-! # Dispatch and public-length checks for the signature encoder -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86
open VG VG.X86 VG.Proof.Mont.X86
open VG.Impl.RsaPkcs1Sig.X86 Spec.RsaPkcs1Sig

theorem sub_beq32 (a b : BitVec 32) : (a - b == 0) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    have add := congrArg (fun x => x + b) h
    simpa only [BitVec.sub_add_cancel, show (0 : BitVec 32) = 0#32 from rfl, BitVec.zero_add] using add
  · intro h
    rw [h, BitVec.sub_self]
    rfl

/-- `s'` is `s` but for the flags. -/
def SameF (s s' : State) : Prop := s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem cmp_ok (s : State) (i : Nat) :
    WP isa (.block [.alu .cmp .edx (.imm (BitVec.ofNat 32 i))]) s fun t => SameF s t ∧
      t.zf = some (s.gpr .edx == BitVec.ofNat 32 i) := by
  refine VG.Proof.Mont.X86.wp_cmpS rfl fun t F Z => WP.block_nil ?_
  exact ⟨⟨F.gpr, F.mem, F.rd, F.wr⟩, Z.trans (congrArg some (sub_beq32 _ _))⟩

/-- `dispatch c d hs i`: `c (i + j) h` if `rdx`'s low 32 bits are `i + j`
for the `j`-th function `h` of `hs`, `d` if they are none of them, from a
state but for the flags. -/
theorem dispatch_ok (c : Nat → Hash → Prog isa) (d : Prog isa) {Q : State → Prop} {s₀ : State}
    (x : BitVec 32) (hx : s₀.gpr .edx = x) :
    ∀ (hs : List Hash) (i : Nat), i + hs.length < 2 ^ 32 →
      (∀ j (h : j < hs.length), x.toNat = i + j → ∀ s, SameF s₀ s → WP isa (c (i + j) hs[j]) s Q) →
      ((∀ j < hs.length, x.toNat ≠ i + j) → ∀ s, SameF s₀ s → WP isa d s Q) →
      ∀ s, SameF s₀ s → WP isa (dispatch c d hs i) s Q := by
  intro hs
  induction hs with
  | nil => intro i _ _ hd s hs; exact hd (fun _ h => absurd h (Nat.not_lt_zero _)) s hs
  | cons h hs ih =>
    intro i hi hc hd s hs₀
    refine WP.seq (WP.mono (cmp_ok s i) fun t ⟨ht, hz⟩ => ?_)
    have hst : SameF s₀ t := ⟨ht.1.trans hs₀.1, ht.2.1.trans hs₀.2.1, ht.2.2.1.trans hs₀.2.2.1,
      ht.2.2.2.trans hs₀.2.2.2⟩
    have hrdx : s.gpr .edx = x := by rw [hs₀.1]; exact hx
    rw [hrdx] at hz
    by_cases he : x.toNat = i
    · have hxe : x = BitVec.ofNat 32 i := by
        apply BitVec.eq_of_toNat_eq; rw [he, BitVec.toNat_ofNat]; simp at hi; omega
      refine WP.ite true (by simp [eval, hz, hxe]) (fun _ => ?_) (by simp)
      exact hc 0 (by simp) (by simpa using he) t hst
    · have hxe : x ≠ BitVec.ofNat 32 i := by
        intro h'; apply he; rw [h', BitVec.toNat_ofNat]; simp at hi; omega
      refine WP.ite false (by simp [eval, hz, hxe]) (by simp) (fun _ => ?_)
      refine ih (i + 1) (by simp at hi; omega) (fun j hj hxj t' ht' => ?_) (fun hn t' ht' => ?_) t hst
      · have := hc (j + 1) (by simp; omega) (by omega) t' ht'
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using this
      · refine hd (fun j hj => ?_) t' ht'
        cases j with
        | zero => simpa using he
        | succ j => have := hn j (by simp at hj; omega); omega


theorem ofId_hashes : ∀ j (h : j < hashes.length), Hash.ofId j = some hashes[j] := by decide

theorem ofId_ge {j : Nat} (h : hashes.length ≤ j) : Hash.ofId j = none := by
  unfold Hash.ofId
  split <;> simp_all [hashes]

theorem hashes_length : hashes.length = 12 := rfl

theorem prefix_length_le (h : Hash) : h.prefix.length + h.len ≤ 83 := by cases h <;> decide

theorem lens_ok (h : Hash) (s : State) :
    WP isa (lens h) s fun t => t.mem = s.mem ∧ Keeps [.eax, .ebx] s t ∧
      t.gpr .ebx = BitVec.ofNat 32 (h.prefix.length + h.len) ∧ t.gpr .eax = BitVec.ofNat 32 h.len := by
  unfold lens
  refine wp_movS rfl fun u U _ => ?_
  refine wp_movS rfl fun t T _ => WP.block_nil ?_
  exact ⟨T.mem.trans U.mem, (U.keeps.mono (by decide)).trans (T.keeps.mono (by decide)),
    (T.other .ebx (by decide)).trans U.gpr, T.gpr⟩

theorem W_sameF {s0 s t : State} {acc : List Byte} (h : W s0 acc s) (ht : SameF s t) : W s0 acc t := by
  refine ⟨?_, ht.2.1.trans h.mem, ?_⟩
  · exact ⟨fun r hr => by rw [ht.1]; exact h.rest.1 r hr,
      ht.2.2.1.trans h.rest.2.1, ht.2.2.2.trans h.rest.2.2⟩
  · rw [ht.1]; exact h.cursor

end VG.Proof.RsaPkcs1Sig.X86
