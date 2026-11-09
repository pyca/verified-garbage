module

public import VerifiedGarbage.Impl.AesXts.PPC64LE
public import VerifiedGarbage.Proof.Aes.PPC64LE.Crypto.Rounds
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Vector
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: the rounds with keys in registers, which the groups' proofs (`Verified.lean`) use.
/-!
# XTS-AES on PPC64LE: the rounds with round keys 1–9 in registers

`aesRes_ok`: `aesRes` computes what `Impl.Aes.PPC64LE.Crypto.aes` does
(`aes_ok`), for AES-128, -192 and -256, when `kreg i` holds round key `i`
for `i` from 1 to 9. The middle rounds are counted as in `aes_ok`'s
`middle`: `resident_ok` runs one with a key in a register, `streamed_ok`
one with a key loaded from the schedule.
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE

open VG VG.PPC64LE
open VG.Impl.AesXts.PPC64LE (kreg streamed residents extra aesRes)
open VG.Impl.Aes.PPC64LE.Crypto (key mask byteMask)
open VG.Proof.Aes.PPC64LE.Crypto
open VG.Spec.Aes (roundKey)

theorem kreg_mem (i : Nat) :
    kreg i ∈ ([.v10, .v11, .v12, .v13, .v14, .v15, .v16, .v17, .v18] : List VReg) := by
  unfold kreg; split <;> simp

theorem kreg_ne_key (i : Nat) : kreg i ≠ key := by
  have := kreg_mem i; intro h; rw [h] at this; simp [key] at this

theorem kreg_ne_mask (i : Nat) : kreg i ≠ mask := by
  have := kreg_mem i; intro h; rw [h] at this; simp [mask] at this

/-- After `j` middle rounds. -/
structure SInv (inverse : Bool) (rs : List VReg) (s₀ : State) (nr j : Nat) (s : State) : Prop where
  effects : Local [.r9, .r10, .r12] (key :: rs) s₀ s
  val : ∀ b ∈ rs, aesState (s.vpr b) = middle inverse nr (schedule nr s₀) (aesState (s₀.vpr b)) j

theorem SInv.zero {inverse : Bool} {rs : List VReg} {s₀ s : State} {nr : Nat} (h : SInv inverse rs s₀ nr 0 s) :
    s.gpr .r0 = s₀.gpr .r0 := h.effects.keep.gpr (by decide)

/-- A middle round with the key in `kreg i`. -/
theorem resident_ok (inverse : Bool) (rs : List VReg) (hn : rs.Nodup) (hkr : ∀ i, kreg i ∉ rs)
    {s₀ s : State} {nr j i : Nat} (h : SInv inverse rs s₀ nr j s)
    (hk : IsKey (s₀.vpr (kreg i)) (roundKey (schedule nr s₀) (keyIndex inverse nr (j + 1)))) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.cipherRegs inverse false (kreg i) rs)) s
      (SInv inverse rs s₀ nr (j + 1)) := by
  have hks : s.vpr (kreg i) = s₀.vpr (kreg i) :=
    h.effects.v _ (by simp [kreg_ne_key i, hkr i])
  refine WP.mono (vector_map (fun b => .vop (.cipher inverse false b b (kreg i))) (vcipher inverse false) (kreg i)
      (fun _ _ => rfl) rs s hn (hkr i)) fun t ⟨hv, ho⟩ => ⟨?_, fun b hb => ?_⟩
  · exact (h.effects.trans (Local.of_vector ho)).weaken (by simp) fun r hr => by
      simp only [List.mem_append, List.mem_cons] at hr ⊢
      rcases hr with (h | h) | h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inr h
  · rw [hv b hb, hks, vcipher_transform inverse false hk, h.val b hb]
    exact middle_succ inverse nr (schedule nr s₀) (aesState (s₀.vpr b)) j

/-- A middle round with round key `i`, loaded from the schedule. -/
theorem streamed_ok (inverse : Bool) (rs : List VReg) (hn : rs.Nodup) (hk : key ∉ rs) (hm : mask ∉ rs)
    {s₀ s : State} {nr j i : Nat} (hp : Inputs nr s₀) (h : SInv inverse rs s₀ nr j s)
    (hi : keyIndex inverse nr (j + 1) = i) (hin : i ≤ nr) :
    WP isa (.block (streamed inverse rs i)) s (SInv inverse rs s₀ nr (j + 1)) := by
  have hmax := hp.max
  have r3 : s.gpr .r3 = s₀.gpr .r3 := h.effects.keep.gpr (by decide)
  rw [streamed]
  refine WP.cons (exec_addi' (d := .r9) (n := .r3) (imm := 16 * i) (by omega)) ?_
  have h9 : (s.write .r9 (s.gpr .r3 + BitVec.ofNat 64 (16 * i))).gpr .r9 = s₀.gpr .r3 + BitVec.ofNat 64 (16 * i) := by
    rw [RegUpd.gpr_write_self, r3]
  have hz : (s.write .r9 (s.gpr .r3 + BitVec.ofNat 64 (16 * i))).gpr .r0 = 0 := by
    rw [RegUpd.gpr_write, ite_eq_right (by decide), h.effects.keep.gpr (by decide), hp.zero]
  have hmk : (s.write .r9 (s.gpr .r3 + BitVec.ofNat 64 (16 * i))).vpr mask = byteMask := by
    rw [vpr_write, h.effects.v _ (by simp [hm, key, mask]), hp.mask]
  have hr : InRegions ((s.write .r9 (s.gpr .r3 + BitVec.ofNat 64 (16 * i))).rd ++
      (s.write .r9 (s.gpr .r3 + BitVec.ofNat 64 (16 * i))).wr)
      ((s.write .r9 (s.gpr .r3 + BitVec.ofNat 64 (16 * i))).gpr .r9) 16 := by
    rw [RegUpd.rd_write, RegUpd.wr_write, h9, h.effects.keep.2.1, h.effects.keep.2.2]
    exact hp.reads i hin
  have hkey : IsKey (rev128 ((s.write .r9 (s.gpr .r3 + BitVec.ofNat 64 (16 * i))).mem.read
      ((s.write .r9 (s.gpr .r3 + BitVec.ofNat 64 (16 * i))).gpr .r9) 16))
      (roundKey (schedule nr s₀) (keyIndex inverse nr (j + 1))) := by
    rw [RegUpd.mem_write, h9, h.effects.mem, hi]
    exact key_read s₀.mem (s₀.gpr .r3) (by omega)
  refine WP.mono (round_ok inverse false rs _ hn hk hz hmk hr) fun t ⟨hv, ho⟩ => ⟨?_, fun b hb => ?_⟩
  · have hf := (h.effects.trans (Local.write s .r9 (s.gpr .r3 + BitVec.ofNat 64 (16 * i)))).trans
      (Local.of_vector ho)
    exact hf.weaken (by simp) fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with (h | h) | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inl h
      · exact Or.inr h
  · rw [hv b hb, vcipher_transform inverse false hkey, vpr_write, h.val b hb]
    exact middle_succ inverse nr (schedule nr s₀) (aesState (s₀.vpr b)) j

/-- The nine middle rounds with the keys in registers. -/
theorem residents_ok (inverse : Bool) (rs : List VReg) (hn : rs.Nodup) (hkr : ∀ i, kreg i ∉ rs)
    {s₀ s : State} {nr : Nat} (hnr : 10 ≤ nr)
    (hres : ∀ i, 1 ≤ i → i ≤ 9 → IsKey (s₀.vpr (kreg i)) (roundKey (schedule nr s₀) i))
    (h : SInv inverse rs s₀ nr (if inverse then nr - 10 else 0) s) :
    WP isa (.block (residents inverse rs)) s
      (SInv inverse rs s₀ nr ((if inverse then nr - 10 else 0) + 9)) := by
  refine wp_range_flatMap (M := isa) (fun t => SInv inverse rs s₀ nr ((if inverse then nr - 10 else 0) + t))
    (fun t u ht hu => ?_) 9 (Nat.le_refl _) s h
  refine resident_ok inverse rs hn hkr hu ?_
  have e : keyIndex inverse nr ((if inverse then nr - 10 else 0) + t + 1) = if inverse then 9 - t else t + 1 := by
    cases inverse <;> simp only [keyIndex, Bool.false_eq_true, ite_false, ite_true] <;> omega
  simp only [Nat.add_eq]
  rw [e]
  cases inverse
  · simp only [Bool.false_eq_true, ite_false]
    exact hres (t + 1) (by omega) (by omega)
  · simp only [ite_true]
    exact hres (9 - t) (by omega) (by omega)

/-- `r12` set to `r4 - c`, which is `Nr - c`. -/
theorem sub12_ok (inverse : Bool) (rs : List VReg) {s₀ s : State} {nr j c : Nat} (hp : Inputs nr s₀)
    (hc : c ≤ nr) (hc' : c < 32768) (h : SInv inverse rs s₀ nr j s) :
    WP isa (.block [.subi .r12 .r4 c]) s fun t =>
      SInv inverse rs s₀ nr j t ∧ t.gpr .r12 = BitVec.ofNat 64 (nr - c) := by
  refine WP.cons (exec_subi' (d := .r12) (n := .r4) (imm := c) hc') (wp_nil ⟨⟨?_, fun b hb => ?_⟩, ?_⟩)
  · exact (h.effects.trans (Local.write s .r12 _)).weaken (by simp) (by simp)
  · rw [vpr_write]; exact h.val b hb
  · rw [RegUpd.gpr_write_self, h.effects.keep.gpr (by decide), hp.rounds, Offset.ofNat_sub_ofNat hc]

/-- The middle rounds with keys 10 to `Nr - 1`. -/
theorem extra_ok (inverse : Bool) (rs : List VReg) (hn : rs.Nodup) (hk : key ∉ rs) (hm : mask ∉ rs)
    {s₀ s : State} {nr : Nat} (hp : Inputs nr s₀) (hR : nr = 10 ∨ nr = 12 ∨ nr = 14)
    (h : SInv inverse rs s₀ nr (if inverse then 0 else 9) s) :
    WP isa (extra inverse rs) s (SInv inverse rs s₀ nr ((if inverse then 0 else 9) + (nr - 10))) := by
  have hmax := hp.max
  rw [extra]
  refine WP.seq (WP.mono (sub12_ok inverse rs hp (c := 10) (by omega) (by decide) h) fun t ⟨ht, h12⟩ => ?_)
  refine WP.ite (decide (nr - 10 = 0)) (eval_zero_ofNat t .r12 (by omega) h12) (fun hz => ?_) (fun hz => ?_)
  · exact WP.block_nil (by rw [show nr - 10 = 0 by simpa using hz, Nat.add_zero]; exact ht)
  · have hnz : nr ≠ 10 := by simp at hz; omega
    cases inverse
    · simp only [Bool.false_eq_true, ite_false] at ht ⊢
      refine WP.seq (WP.mono (?_ : WP isa (.block (streamed false rs 10 ++ streamed false rs 11)) t
        (SInv false rs s₀ nr 11)) fun u hu => ?_)
      · rw [WP.block_append_iff]
        exact WP.mono (streamed_ok false rs hn hk hm hp ht (by simp [keyIndex]) (by omega)) fun u hu =>
          streamed_ok false rs hn hk hm hp hu (by simp [keyIndex]) (by omega)
      refine WP.seq (WP.mono (sub12_ok false rs hp (c := 12) (by omega) (by decide) hu) fun v ⟨hv, h12⟩ => ?_)
      refine WP.ite (decide (nr - 12 = 0)) (eval_zero_ofNat v .r12 (by omega) h12) (fun hz => ?_) (fun hz => ?_)
      · exact WP.block_nil (by rw [show 9 + (nr - 10) = 11 by simp at hz; omega]; exact hv)
      · have e : nr = 14 := by simp at hz; omega
        subst e
        rw [WP.block_append_iff]
        exact WP.mono (streamed_ok false rs hn hk hm hp hv (by simp [keyIndex]) (by omega)) fun w hw =>
          streamed_ok false rs hn hk hm hp hw (by simp [keyIndex]) (by omega)
    · simp only [ite_true] at ht ⊢
      refine WP.seq (WP.mono (?_ : WP isa (.seq (.block [.subi .r12 .r4 12])
          (.ite (.zero .d .r12) (.block []) (.block (streamed true rs 13 ++ streamed true rs 12)))) t
        (SInv true rs s₀ nr (nr - 12))) fun u hu => ?_)
      · refine WP.seq (WP.mono (sub12_ok true rs hp (c := 12) (by omega) (by decide) ht) fun v ⟨hv, h12⟩ => ?_)
        refine WP.ite (decide (nr - 12 = 0)) (eval_zero_ofNat v .r12 (by omega) h12) (fun hz => ?_) (fun hz => ?_)
        · exact WP.block_nil (by rw [show nr - 12 = 0 by simpa using hz]; exact hv)
        · have e : nr = 14 := by simp at hz; omega
          subst e
          rw [WP.block_append_iff]
          exact WP.mono (streamed_ok true rs hn hk hm hp hv (by simp [keyIndex]) (by omega)) fun w hw =>
            streamed_ok true rs hn hk hm hp hw (by simp [keyIndex]) (by omega)
      · rw [WP.block_append_iff, show 0 + (nr - 10) = nr - 12 + 1 + 1 by omega]
        exact WP.mono (streamed_ok true rs hn hk hm hp hu (by simp [keyIndex]; omega) (by omega)) fun w hw =>
          streamed_ok true rs hn hk hm hp hw (by simp [keyIndex]; omega) (by omega)

/-- The last round, with key `Nr` (key 0 when deciphering). -/
theorem final_ok (inverse : Bool) (rs : List VReg) (hn : rs.Nodup) (hk : key ∉ rs) (hm : mask ∉ rs)
    {s₀ s : State} {nr : Nat} (hp : Inputs nr s₀) (h : SInv inverse rs s₀ nr (nr - 1) s) :
    WP isa (.block (Impl.Aes.PPC64LE.Crypto.keyStart (!inverse) ++ Impl.Aes.PPC64LE.Crypto.round inverse true rs)) s
      fun t => (∀ b ∈ rs, aesState (t.vpr b) = result inverse nr (schedule nr s₀) (aesState (s₀.vpr b))) ∧
        Local [.r9, .r10, .r12] (key :: rs) s₀ t := by
  have hmax := hp.max
  have hmin := hp.min
  rw [WP.block_append_iff]
  refine WP.mono (start_run (!inverse) s) fun u hu => ?_
  subst hu
  have r3 : s.gpr .r3 = s₀.gpr .r3 := h.effects.keep.gpr (by decide)
  have r4 : s.gpr .r4 = BitVec.ofNat 64 nr := (h.effects.keep.gpr (by decide)).trans hp.rounds
  have h9 : (s.write .r9 (if !inverse then s.gpr .r3 + (s.gpr .r4 <<< 4) else s.gpr .r3)).gpr .r9 =
      s₀.gpr .r3 + BitVec.ofNat 64 (16 * keyIndex inverse nr nr) := by
    rw [RegUpd.gpr_write_self, r3, r4]
    cases inverse
    · simp only [Bool.not_false, ite_true, keyIndex, Bool.false_eq_true, ite_false]
      rw [BitVec.shiftLeft_eq_mul_twoPow, show BitVec.twoPow 64 4 = BitVec.ofNat 64 16 from rfl,
        BitVec.ofNat_mul_ofNat, Nat.mul_comm nr 16]
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, keyIndex, ite_true, Nat.sub_self, Nat.mul_zero,
        BitVec.add_zero]
  generalize hw : s.write .r9 (if !inverse then s.gpr .r3 + (s.gpr .r4 <<< 4) else s.gpr .r3) = w at h9
  have lw : Local [.r9] [] s w := hw ▸ Local.write s .r9 _
  have hz : w.gpr .r0 = 0 := by
    rw [lw.keep.gpr (by decide), h.effects.keep.gpr (by decide), hp.zero]
  have hmk : w.vpr mask = byteMask := by
    rw [lw.v _ (by simp), h.effects.v _ (by simp [hm, key, mask]), hp.mask]
  have hidx : keyIndex inverse nr nr ≤ nr := keyIndex_le inverse (Nat.le_refl _)
  have hr : InRegions (w.rd ++ w.wr) (w.gpr .r9) 16 := by
    rw [lw.keep.2.1, lw.keep.2.2, h9, h.effects.keep.2.1, h.effects.keep.2.2]
    exact hp.reads _ hidx
  have hkey : IsKey (rev128 (w.mem.read (w.gpr .r9) 16)) (roundKey (schedule nr s₀) (keyIndex inverse nr nr)) := by
    rw [lw.mem, h.effects.mem, h9]
    exact key_read s₀.mem (s₀.gpr .r3) (by omega)
  refine WP.mono (round_ok inverse true rs w hn hk hz hmk hr) fun t ⟨hv, ho⟩ => ⟨fun b hb => ?_, ?_⟩
  · rw [hv b hb, vcipher_transform inverse true hkey, lw.v _ (by simp), h.val b hb]
    have e := middle_last inverse nr (schedule nr s₀) (aesState (s₀.vpr b))
    exact e
  · exact ((h.effects.trans lw).trans (Local.of_vector ho)).weaken (by simp) fun r hr => by
      simp only [List.append_nil, List.mem_append] at hr
      exact hr.elim id id

/-- `aesRes` computes AES, as `aes_ok` states of `aes`, with round keys
1–9 in `kreg 1` … `kreg 9`. -/
theorem aesRes_ok (inverse : Bool) (rs : List VReg) (hn : rs.Nodup) (hk : key ∉ rs) (hm : mask ∉ rs)
    (hkr : ∀ i, kreg i ∉ rs) {s : State} {nr : Nat} (hp : Inputs nr s) (hR : nr = 10 ∨ nr = 12 ∨ nr = 14)
    (hres : ∀ i, 1 ≤ i → i ≤ 9 → IsKey (s.vpr (kreg i)) (roundKey (schedule nr s) i)) :
    WP isa (aesRes inverse rs) s fun t =>
      (∀ b ∈ rs, aesState (t.vpr b) = result inverse nr (schedule nr s) (aesState (s.vpr b))) ∧
      Local [.r9, .r10, .r12] (key :: rs) s t := by
  have hnr : 10 ≤ nr := by omega
  rw [aesRes]
  refine WP.seq (WP.mono (initialBody_ok inverse rs hn hk hp) fun t ht => ?_)
  have h0 : SInv inverse rs s nr 0 t := ⟨ht.effects.weaken (by simp) (fun _ h => h), ht.val⟩
  refine WP.seq (WP.mono (?_ : WP isa (if inverse then .seq (extra true rs) (.block (residents true rs))
      else .seq (.block (residents false rs)) (extra false rs)) t (SInv inverse rs s nr (nr - 1)))
    fun u hu => final_ok inverse rs hn hk hm hp hu)
  cases inverse
  · simp only [Bool.false_eq_true, ite_false]
    refine WP.seq (WP.mono (residents_ok false rs hn hkr hnr hres (by simpa using h0)) fun u hu => ?_)
    refine WP.mono (extra_ok false rs hn hk hm hp hR (by simpa using hu)) fun v hv => ?_
    simp only [Bool.false_eq_true, ite_false] at hv
    rwa [show 9 + (nr - 10) = nr - 1 by omega] at hv
  · simp only [ite_true]
    refine WP.seq (WP.mono (extra_ok true rs hn hk hm hp hR (by simpa using h0)) fun u hu => ?_)
    refine WP.mono (residents_ok true rs hn hkr hnr hres (by simpa using hu)) fun v hv => ?_
    simp only [ite_true] at hv
    rwa [show nr - 10 + 9 = nr - 1 by omega] at hv

end VG.Proof.AesXts.PPC64LE
