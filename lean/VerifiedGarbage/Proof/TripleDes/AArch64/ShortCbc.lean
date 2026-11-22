module

public import VerifiedGarbage.Impl.TripleDes.AArch64.Short
public import VerifiedGarbage.Proof.TripleDes.AArch64.ShortEcb
public import VerifiedGarbage.Proof.TripleDes.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Modes.Cbc
public import VerifiedGarbage.Proof.Cmac.Mem
public import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Modes.CbcNext
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Update
import VerifiedGarbage.Proof.CmacTripleDes.Bytes
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.TripleDes.AArch64.Bytes
import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.TripleDes.AArch64.CbcLit
import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
meta import VerifiedGarbage.Proof.TripleDes.AArch64.FbVerified
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.TripleDes.AArch64.Short
meta import VerifiedGarbage.Proof.TripleDes.AArch64.CbcLit

/-!
# Triple DES-CBC decryption on AArch64: a few blocks through the table block

`cbc_wp`: `Short.cbcDecrypt` is CBC decryption that updates the chaining
value, by the loop invariant `CInv` over the decrypting table block
(`dec_ok`). `cbcDecryptChained_verified`: `Short.cbcDecryptChained`, which
runs it for fewer than eleven blocks and the batched code otherwise, meets
the batched code's contract, whichever `few` runs, and is constant time by
the taint analysis of the whole function.
-/

@[expose] public section

namespace VG.Impl.TripleDes.AArch64.Short
materialize_code cbcDecryptChained
end VG.Impl.TripleDes.AArch64.Short

namespace VG.Proof.TripleDes.AArch64.Short.Cbc

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Impl.CmacTripleDes.AArch64 (mov prep enc dec)
open VG.Impl.TripleDes.AArch64.Short
open VG.Proof.CmacTripleDes VG.Proof.CmacTripleDes.AArch64
open VG.Proof.Modes (cbcOut cbcPrev)
open VG.Proof.Cmac (le8 le8_readW le8_xor bytesAt_frame)
open VG.Spec.Aes (bytesAt)

abbrev W (s : State) : Addr := s.gpr .x0
abbrev P (s : State) : Addr := s.gpr .x1
abbrev D (s : State) : Addr := s.gpr .x2
abbrev N (s : State) : Nat := (s.gpr .x3).toNat
abbrev S (s : State) : Addr := s.gpr .x4
abbrev keyR (s : State) : Region := ⟨W s, 384⟩
abbrev ivR (s : State) : Region := ⟨P s, 8⟩
abbrev dataR (s : State) : Region := ⟨D s, 8 * N s⟩
abbrev scrR (s : State) : Region := ⟨S s, 8 * 140⟩
abbrev changes (s : State) : List Region := [ivR s, dataR s, ⟨S s, 456⟩]
abbrev K (s : State) : Spec.TripleDes.Schedule := Spec.TripleDes.scheduleAt s.mem (W s)
abbrev invC (s : State) : Spec.Cbc.Cipher := Spec.TripleDes.invCipher (K s)
abbrev iv (s : State) : List Byte := bytesAt s.mem (P s) 8

/-- The batched functions' precondition (`batchPre blkLen`). -/
structure Pre (s : State) : Prop where
  rd : s.rd = [keyR s]
  wr : s.wr = [ivR s, dataR s, scrR s]
  key_iv : (keyR s).Disjoint (ivR s)
  key_data : (keyR s).Disjoint (dataR s)
  key_scr : (keyR s).Disjoint (scrR s)
  iv_data : (ivR s).Disjoint (dataR s)
  iv_scr : (ivR s).Disjoint (scrR s)
  data_scr : (dataR s).Disjoint (scrR s)
  data_fit : (D s).toNat + 8 * N s ≤ 2 ^ 64

structure CInv (s₀ : State) (k : Nat) (s : State) : Prop where
  x14 : s.gpr .x14 = W s₀
  x15 : s.gpr .x15 = S s₀
  x1 : s.gpr .x1 = P s₀
  x2 : s.gpr .x2 = D s₀ + BitVec.ofNat 64 (8 * k)
  x3 : s.gpr .x3 = BitVec.ofNat 64 (N s₀ - k)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame (changes s₀) s₀.mem s.mem
  consts : Consts s
  masks : Masks s
  keys : ∀ i < 48, s.mem.readW (S s₀ + BitVec.ofNat 64 (8 * i)) 64 = spread ((K s₀).getD i 0)
  slots : VG.AArch64.Spill.Saved (S s₀) s₀.gpr saveSlots s.mem
  data : ∀ j < N s₀, bytesAt s.mem (D s₀ + BitVec.ofNat 64 (8 * j)) 8 =
    if j < k then cbcOut 8 (invC s₀) s₀.mem (D s₀) (iv s₀) j
    else bytesAt s₀.mem (D s₀ + BitVec.ofNat 64 (8 * j)) 8
  state : bytesAt s.mem (P s₀) 8 = cbcPrev 8 s₀.mem (D s₀) (iv s₀) k

section
variable {s₀ : State}

theorem scr_sub {d n : Nat} (h : d + n ≤ 1120) :
    Region.Sub ⟨S s₀ + BitVec.ofNat 64 d, n⟩ (scrR s₀) := Offset.sub_base _ h

theorem data_sub {j : Nat} (hj : j < N s₀) :
    Region.Sub ⟨D s₀ + BitVec.ofNat 64 (8 * j), 8⟩ (dataR s₀) := Offset.sub_base _ (by omega_using [hj])

theorem sched_frame (hp : Pre s₀) {m : Mem} (hf : Frame (changes s₀) s₀.mem m) :
    Spec.TripleDes.scheduleAt m (W s₀) = K s₀ :=
  scheduleAt_frame hf fun r hr => by
    simp only [changes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.key_iv
    · exact hp.key_data
    · exact hp.key_scr.sub_right (Region.sub_prefix (by decide))

theorem block_pre (hp : Pre s₀) {s : State} (h14 : s.gpr .x14 = W s₀) (h15 : s.gpr .x15 = S s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) : BlockPre s where
  sched := ⟨keyR s₀, by rw [hrd, hwr, hp.rd]; simp, by rw [h14], by show 384 ≤ 384; decide,
    by show 384 < 2 ^ 64; decide⟩
  scr := ⟨scrR s₀, by rw [hwr, hp.wr]; simp, by rw [h15], by show 456 ≤ 8 * 140; decide,
    by show 8 * 140 < 2 ^ 64; decide⟩
  disj := by rw [h14, h15]; exact hp.key_scr.symm.sub_left (Region.sub_prefix (by decide))

end

/-- The decryption of the bytes of a word is the bytes of a word. -/
theorem invCipher_le8 (S : Spec.TripleDes.Schedule) (w : BitVec 64) :
    Spec.TripleDes.invCipher S (le8 w) = le8 (byteRev64 (tdesDec S (byteRev64 w))) := by
  rw [Spec.TripleDes.invCipher, Spec.TripleDes.decryptBlock, decode_le8, encode_le8]
  rfl

/-- The ciphertext block at `x2` into `x5`, as the integer the table block takes. -/
theorem cbcLoad_ok (s : State) {q : Addr} (hq : s.gpr .x2 = q) (rq : InRegions (s.rd ++ s.wr) q 8) :
    ∃ s', runBlock isa cbcLoad s = some s' ∧
      s'.gpr .x5 = byteRev64 (s.mem.readW q 64) ∧
      (∀ r, r ≠ .x5 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v := by
  obtain rq' : InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero, hq]; exact rq
  let s₁ := s.write .x .x5 (s.mem.readW (s.gpr .x2 + BitVec.ofNat 64 0) 64)
  let s₂ := s₁.write .x .x5 (rev64 (s₁.read .x .x5))
  refine ⟨s₂, by
    rw [cbcLoad, runBlock_cons, exec_ldr_x (by decide) rq', runStep_some, runBlock_cons, exec_rev,
      runStep_some, runBlock_nil], ?_, fun r h => ?_, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [s₂, s₁, State.read, gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero, hq]
    rfl
  · simp only [s₂, s₁, gpr_write_of_ne _ _ _ h]

/-- The plaintext block and the next chaining value, and on to the next block. -/
theorem cbcStore_ok (s : State) {p q : Addr} (hp : s.gpr .x1 = p) (hq : s.gpr .x2 = q)
    (wp : InRegions s.wr p 8) (wq : InRegions s.wr q 8) :
    ∃ s', runBlock isa cbcStore s = some s' ∧
      s'.gpr .x2 = s.gpr .x2 + 8 ∧ s'.gpr .x3 = s.gpr .x3 - 1 ∧
      (∀ r, r ∉ [Reg.x2, .x3, .x5, .x6] → s'.gpr r = s.gpr r) ∧
      s'.mem = (s.mem.writeW p (s.mem.readW q 64)).writeW q
        (byteRev64 (s.gpr .x5) ^^^ s.mem.readW p 64) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.v = s.v := by
  have inrw {a : Addr} (h : InRegions s.wr a 8) : InRegions (s.rd ++ s.wr) a 8 := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩
  let s₁ := s.write .x .x5 (rev64 (s.read .x .x5))
  obtain r₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x1 + BitVec.ofNat 64 0) 8 := by
    rw [BitVec.add_zero, gpr_write_of_ne _ _ _ (by decide), hp]; exact inrw wp
  let s₂ := s₁.write .x .x6 (s₁.mem.readW (s₁.gpr .x1 + BitVec.ofNat 64 0) 64)
  let s₃ := s₂.write .x .x5 (s₂.read .x .x5 ^^^ s₂.read .x .x6)
  obtain r₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .x2 + BitVec.ofNat 64 0) 8 := by
    simp only [s₃, s₂, s₁, BitVec.add_zero, gpr_write_of_ne _ _ _ (by decide : Reg.x2 ≠ .x5),
      gpr_write_of_ne _ _ _ (by decide : Reg.x2 ≠ .x6), hq]
    exact inrw wq
  let s₄ := s₃.write .x .x6 (s₃.mem.readW (s₃.gpr .x2 + BitVec.ofNat 64 0) 64)
  obtain w₄ : InRegions s₄.wr (s₄.gpr .x1 + BitVec.ofNat 64 0) 8 := by
    simp only [s₄, s₃, s₂, s₁, BitVec.add_zero, gpr_write_of_ne _ _ _ (by decide : Reg.x1 ≠ .x5),
      gpr_write_of_ne _ _ _ (by decide : Reg.x1 ≠ .x6), hp]
    exact wp
  let s₅ : State := { s₄ with mem := s₄.mem.writeW (s₄.gpr .x1 + BitVec.ofNat 64 0) (s₄.gpr .x6) }
  obtain w₅ : InRegions s₅.wr (s₅.gpr .x2 + BitVec.ofNat 64 0) 8 := by
    change InRegions s.wr (s₄.gpr .x2 + BitVec.ofNat 64 0) 8
    simp only [s₄, s₃, s₂, s₁, BitVec.add_zero, gpr_write_of_ne _ _ _ (by decide : Reg.x2 ≠ .x5),
      gpr_write_of_ne _ _ _ (by decide : Reg.x2 ≠ .x6), hq]
    exact wq
  refine ⟨_, by
    rw [cbcStore, runBlock_cons, exec_rev, runStep_some, runBlock_cons,
      exec_ldr_x (by decide) r₁, runStep_some, runBlock_cons, exec_logic, runStep_some,
      runBlock_cons, exec_ldr_x (by decide) r₃, runStep_some, runBlock_cons,
      exec_str_x (by decide) w₄, runStep_some, runBlock_cons, exec_str_x (by decide) w₅,
      runStep_some, runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp [s₅, s₄, s₃, s₂, s₁, gpr_write, State.read]
  · simp [s₅, s₄, s₃, s₂, s₁, gpr_write, State.read]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [s₅, s₄, s₃, s₂, s₁, gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]
  · simp only [s₅, s₄, s₃, s₂, s₁, mem_write, State.read, gpr_write, BitVec.setWidth_eq, hp, hq,
      BitVec.add_zero, reduceCtorEq, ↓reduceIte]
    rfl

/-- One block, after the setup the blocks share. -/
theorem body_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : CInv s₀ k s) :
    WP isa (.seq (.block cbcLoad) (.seq dec (.block cbcStore))) s (CInv s₀ (k + 1)) := by
  obtain hN : N s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  have hdw := hp.data_fit
  obtain rdwr : s.rd ++ s.wr = [keyR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  obtain inData : (dataR s₀).Contains (D s₀ + BitVec.ofNat 64 (8 * k)) 8 :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk, hdw])
  obtain ⟨s₁, run₁, ax₁, keep₁, sp₁, mem₁, rd₁, wr₁, vec₁⟩ := cbcLoad_ok s h.x2
    (by rw [rdwr]; exact in_rw (r := dataR s₀) (by simp) inData)
  obtain x14₁ : s₁.gpr .x14 = W s₀ := by rw [keep₁ _ (by decide), h.x14]
  obtain x15₁ : s₁.gpr .x15 = S s₀ := by rw [keep₁ _ (by decide), h.x15]
  obtain bp : BlockPre s₁ := block_pre hp x14₁ x15₁ (rd₁.trans h.rd) (wr₁.trans h.wr)
  obtain sch₁ : sch s₁ = K s₀ := by rw [sch, x14₁, mem₁]; exact sched_frame hp h.frame
  obtain ready : TInv s₁ s₁ := ⟨Same.refl _, rfl, rfl, h.consts.congr (fun w _ _ _ _ => by rw [vec₁]),
    h.masks.congr (fun p hp' => keep₁ _ (maskRegs_ne p hp').1),
    fun i hi => by rw [x15₁, sch₁, mem₁]; exact h.keys i hi⟩
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (dec_ok bp ready) fun s₂ ⟨same₂, x14₂, ax₂, const₂, mask₂, keys₂⟩ => ?_)
  obtain fr₂ : Frame [⟨S s₀, 384⟩] s.mem s₂.mem := by rw [← mem₁, ← x15₁]; exact same₂.frame
  obtain wr₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [same₂.wr, wr₁, h.wr, hp.wr]
  obtain x1₂ : s₂.gpr .x1 = P s₀ := by
    rw [same₂.keep .x1 (by simp [outer]), keep₁ _ (by decide), h.x1]
  obtain x2₂ : s₂.gpr .x2 = D s₀ + BitVec.ofNat 64 (8 * k) := by
    rw [same₂.keep .x2 (by simp [outer]), keep₁ _ (by decide), h.x2]
  obtain ⟨s₃, run₃, x2₃, x3₃, keep₃, mem₃, sp₃, rd₃, wr₃, vec₃⟩ := cbcStore_ok s₂ x1₂ x2₂
    (by rw [wr₂]; exact in_rw (r := ivR s₀) (by simp) (Region.contains_self _ _))
    (by rw [wr₂]; exact in_rw (r := dataR s₀) (by simp) inData)
  obtain vals₂ : ∀ j < N s₀, bytesAt s₂.mem (D s₀ + BitVec.ofNat 64 (8 * j)) 8 =
      if j < k then cbcOut 8 (invC s₀) s₀.mem (D s₀) (iv s₀) j
      else bytesAt s₀.mem (D s₀ + BitVec.ofNat 64 (8 * j)) 8 := by
    intro j hj
    rw [bytesAt_frame fr₂ (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (hp.data_scr.sub_left (data_sub hj)).sub_right (Region.sub_prefix (by decide))) (by decide)]
    exact h.data j hj
  obtain ivs₂ : bytesAt s₂.mem (P s₀) 8 = cbcPrev 8 s₀.mem (D s₀) (iv s₀) k := by
    rw [bytesAt_frame fr₂ (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))) (by decide)]
    exact h.state
  obtain ct : bytesAt s.mem (D s₀ + BitVec.ofNat 64 (8 * k)) 8 =
      bytesAt s₀.mem (D s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [h.data k hk, ite_eq_right (Nat.lt_irrefl _)]
  obtain ct₂ : le8 (s₂.mem.readW (D s₀ + BitVec.ofNat 64 (8 * k)) 64) =
      bytesAt s₀.mem (D s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [le8_readW, vals₂ k hk, ite_eq_right (Nat.lt_irrefl _)]
  obtain value : le8 (byteRev64 (s₂.gpr .x5) ^^^ s₂.mem.readW (P s₀) 64) =
      cbcOut 8 (invC s₀) s₀.mem (D s₀) (iv s₀) k := by
    rw [le8_xor, ax₂, ax₁, sch₁, ← invCipher_le8, le8_readW, le8_readW, ct, ivs₂]
    rfl
  let mid := s₂.mem.writeW (P s₀) (s₂.mem.readW (D s₀ + BitVec.ofNat 64 (8 * k)) 64)
  obtain fIv : Frame [ivR s₀] s₂.mem mid :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain fData : Frame [⟨D s₀ + BitVec.ofNat 64 (8 * k), 8⟩] mid s₃.mem := by
    rw [mem₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  obtain fStore : Frame [ivR s₀, ⟨D s₀ + BitVec.ofNat 64 (8 * k), 8⟩] s₂.mem s₃.mem :=
    (fIv.mono (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact List.mem_cons_self)).trans
      (fData.mono (fun _ hr => List.mem_cons_of_mem _ hr))
  obtain stD : ∀ {d n : Nat}, d + n ≤ 1120 → ∀ r ∈ [ivR s₀, ⟨D s₀ + BitVec.ofNat 64 (8 * k), 8⟩],
      (⟨S s₀ + BitVec.ofNat 64 d, n⟩ : Region).Disjoint r := by
    intro d n hdn r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (hp.iv_scr.sub_right (scr_sub hdn)).symm
    · obtain rfl := List.mem_singleton.mp hr
      exact ((hp.data_scr.sub_left (data_sub hk)).sub_right (scr_sub hdn)).symm
  refine WP.of_runBlock ⟨s₃, run₃, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [keep₃ _ (by decide), x14₂, x14₁]
  · rw [keep₃ _ (by decide), same₂.x15, x15₁]
  · rw [keep₃ _ (by decide), x1₂]
  · rw [x2₃, x2₂]
    exact x2_succ _ _
  · rw [x3₃, same₂.keep .x3 (by simp [outer]), keep₁ _ (by decide), h.x3,
      ofNat_sub_one (by omega_using [hk]) (by omega_using [hN])]
    congr 1
  · rw [sp₃, same₂.sp, sp₁, h.sp]
  · rw [rd₃, same₂.rd, rd₁, h.rd]
  · rw [wr₃, same₂.wr, wr₁, h.wr]
  · exact (h.frame.trans (fr₂.sub (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨S s₀, 456⟩, by simp [changes], Region.sub_prefix (by decide)⟩))).trans
        (fStore.sub (fun r hr => by
          rcases List.mem_cons.mp hr with rfl | hr
          · exact ⟨ivR s₀, by simp [changes], fun _ h => h⟩
          · obtain rfl := List.mem_singleton.mp hr
            exact ⟨dataR s₀, by simp [changes], data_sub hk⟩))
  · exact const₂.congr (fun w _ _ _ _ => by rw [vec₃])
  · exact mask₂.congr (fun p hp' => keep₃ _ (by
      obtain ⟨n5, -, -, -, -, n6, -, -, -, -, n2, n3, -⟩ := maskRegs_ne p hp'
      simp [n2, n3, n5, n6]))
  · intro i hi
    rw [fStore.readW (Region.contains_self _ _) (stD (by omega_using [hi])) (by decide)]
    obtain e := keys₂ i hi
    rw [x15₁, sch₁] at e
    exact e
  · exact (h.slots.frame_in (lo := 384) (n := 72) saveSlots_facts.1 fr₂ (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint_base _ (by decide) (by decide))).frame fStore
        (fun q hq => stD (by have := saveSlots_facts.1 q hq; omega_using [this]))
  · intro j hj
    by_cases he : j = k
    · subst j
      rw [mem₃, ← le8_readW, Mem.readW_writeW_self64, value, ite_eq_left (by omega_using [])]
    · rw [bytesAt_frame fData (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact Offset.disjoint (D s₀) (by omega_using [he]) (by omega_using [hdw, hj])
          (by omega_using [hk, hdw])) (by decide),
        bytesAt_frame fIv (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact (hp.iv_data.sub_right (data_sub hj)).symm) (by decide), vals₂ j hj]
      by_cases hlt : j < k
      · rw [ite_eq_left hlt, ite_eq_left (by omega_using [hlt])]
      · rw [ite_eq_right hlt, ite_eq_right (by omega_using [he, hlt])]
  · rw [bytesAt_frame fData (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hp.iv_data.sub_right (data_sub hk)) (by decide)]
    change bytesAt (s₂.mem.writeW _ _) _ 8 = _
    rw [← le8_readW, Mem.readW_writeW_self64, ct₂]
    simp only [cbcPrev, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]

/-- The loop over the blocks. -/
theorem loop_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : CInv s₀ k s) :
    WP isa (.loop (.seq (.block cbcLoad) (.seq dec (.block cbcStore))) (.nonzero .x .x3)) s
      (CInv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (c := .nonzero .x .x3) (Q := CInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ CInv s₀ j t) ?_ (N s₀ - k) s
      ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hk h) fun s' h' => ?_
  obtain hN : N s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  obtain ev := eval_nonzero (r := .x3) (x := N s₀ - (k + 1)) (by omega_using [hN]) h'.x3
  by_cases hz : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show N s₀ = k + 1 by omega_using [hk, hz]]
  · right
    exact ⟨by rw [ev]; simp [hz], N s₀ - (k + 1), by omega_using [hk], k + 1, rfl,
      by omega_using [hz], h'⟩

open VG.Proof.TripleDes.AArch64 (cbcDecAArch64)

theorem result_of_inv {s₀ s : State} (h : CInv s₀ (N s₀) s) (hn : N s₀ ≠ 0) :
    cbcDecAArch64.post s₀ s := by
  constructor
  · change Spec.TripleDes.cbcBlocksAt _ _ _ = Spec.Cbc.decrypt _ _ (Spec.TripleDes.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, cbcBlocksAt_eq]
    obtain hl : (Modes.blocksOf 8 s₀.mem (D s₀) (N s₀)).length = N s₀ := by simp [Modes.blocksOf]
    obtain hg : ∀ j < N s₀, (Modes.blocksOf 8 s₀.mem (D s₀) (N s₀)).getD j [] =
        bytesAt s₀.mem (D s₀ + BitVec.ofNat 64 (8 * j)) 8 :=
      fun j hj => by simp [Modes.blocksOf, List.getD_eq_getElem?_getD, hj]
    rw [Modes.decrypt_eq, hl]
    refine List.map_congr_left fun j hj => ?_
    obtain hj := List.mem_range.mp hj
    rw [h.data j hj, ite_eq_left hj, hg j hj,
      show (if j = 0 then Spec.TripleDes.bytesAt s₀.mem (s₀.gpr .x1) 8
        else (Modes.blocksOf 8 s₀.mem (D s₀) (N s₀)).getD (j - 1) []) =
          cbcPrev 8 s₀.mem (D s₀) (iv s₀) j by
        unfold cbcPrev; split
        · rfl
        · rw [hg _ (Nat.lt_of_le_of_lt (Nat.sub_le j 1) hj)]]
    rfl
  · change bytesAt s.mem (P s₀) 8 = Spec.Cbc.next _ (Spec.TripleDes.cbcBlocksAt _ _ _)
    rw [cbcBlocksAt_eq, Modes.next_blocksOf 8 _ _ _ hn, h.state, cbcPrev, ite_eq_right hn]

/-- CBC decryption over the table block, keeping the registers the block saves. -/
theorem cbc_wp {s₀ : State} (hp : Pre s₀) :
    WP isa cbcDecrypt s₀ fun s =>
      cbcDecAArch64.post s₀ s ∧ ∀ i < 9, s.gpr (VG.Impl.CmacTripleDes.AArch64.savedReg i) = s₀.gpr (VG.Impl.CmacTripleDes.AArch64.savedReg i) := by
  obtain hN : N s₀ < 2 ^ 64 := (s₀.gpr .x3).isLt
  let s₁ := (s₀.write .x .x14 (s₀.gpr .x0)).write .x .x15 ((s₀.write .x .x14 (s₀.gpr .x0)).gpr .x4)
  obtain g₁ : ∀ r, r ≠ .x14 → r ≠ .x15 → s₁.gpr r = s₀.gpr r := fun r h14 h15 => by
    simp only [s₁, gpr_write_of_ne _ _ _ h15, gpr_write_of_ne _ _ _ h14]
  obtain x14₁ : s₁.gpr .x14 = W s₀ := by simp [s₁, gpr_write]
  obtain x15₁ : s₁.gpr .x15 = S s₀ := by simp [s₁, gpr_write]
  change WP isa (.seq _ _) _ _
  refine WP.seq (WP.of_runBlock ⟨s₁, by
    rw [runBlock_cons, exec_mov, runStep_some, runBlock_cons, exec_mov, runStep_some, runBlock_nil], ?_⟩)
  obtain ev := eval_zero (r := .x3) (x := N s₀) hN (by
    rw [g₁ _ (by decide) (by decide)]; simp [N])
  obtain savedNe : ∀ i < 9, VG.Impl.CmacTripleDes.AArch64.savedReg i ≠ .x14 ∧ VG.Impl.CmacTripleDes.AArch64.savedReg i ≠ .x15 := by decide
  by_cases hn : N s₀ = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ⟨?_, fun i hi => ?_⟩)
      (fun h => by cases h)
    · have e : (s₀.gpr .x3).toNat = 0 := hn
      simp [cbcDecAArch64, e, Spec.TripleDes.cbcBlocksAt, Spec.TripleDes.blocksAt, Spec.Cbc.decrypt,
        Spec.Cbc.next, s₁, mem_write]
    · exact g₁ _ (savedNe i hi).1 (savedNe i hi).2
  refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
  obtain bp : BlockPre s₁ := block_pre hp x14₁ x15₁ rfl rfl
  apply WP.seq
  refine WP.mono (prep_ok bp) fun s₂ h₂ => ?_
  obtain outer₂ : ∀ r ∈ outer, s₂.gpr r = s₀.gpr r := by
    intro r hr
    rw [h₂.same.keep r hr]
    simp only [outer, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide)
  obtain hS : sch s₁ = K s₀ := by rw [sch, x14₁]; rfl
  obtain inv₂ : CInv s₀ 0 s₂ := by
    refine ⟨by rw [h₂.x14, x14₁], by rw [h₂.same.x15, x15₁], outer₂ .x1 (by simp [outer]),
      by rw [outer₂ .x2 (by simp [outer])]; exact (BitVec.add_zero _).symm,
      by rw [outer₂ .x3 (by simp [outer])]; simp [N],
      h₂.same.sp, h₂.same.rd, h₂.same.wr, ?_, h₂.consts, h₂.masks, ?_, ?_, ?_, ?_⟩
    · exact h₂.same.frame.sub (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨⟨S s₀, 456⟩, by simp [changes], by rw [x15₁]; exact fun _ h => h⟩)
    · intro i hi
      obtain e := h₂.keys i hi
      rw [x15₁, hS] at e
      exact e
    · intro p hp'
      rw [← x15₁, h₂.slots p hp']
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp'
      exact g₁ _ (savedNe j (List.mem_range.mp hj)).1 (savedNe j (List.mem_range.mp hj)).2
    · intro j hj
      rw [ite_eq_right (Nat.not_lt_zero _)]
      exact bytesAt_frame h₂.same.frame (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        rw [x15₁]
        exact (hp.data_scr.sub_left (data_sub hj)).sub_right (Region.sub_prefix (by decide))) (by decide)
    · change bytesAt s₂.mem (P s₀) 8 = iv s₀
      exact bytesAt_frame h₂.same.frame (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        rw [x15₁]; exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))) (by decide)
  apply WP.seq
  refine WP.mono (loop_ok hp (by omega_using [hn]) inv₂) fun s₃ h₃ => ?_
  refine WP.mono (restore_ok' bp (by rw [h₃.x15, x15₁]) h₃.rd h₃.wr (by
    rw [x15₁]
    intro p hp'
    rw [h₃.slots p hp']
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp'
    exact (g₁ _ (savedNe j (List.mem_range.mp hj)).1 (savedNe j (List.mem_range.mp hj)).2).symm))
    fun s₄ h₄ => ⟨?_, fun i hi => ?_⟩
  · have result := result_of_inv h₃ hn
    simpa only [cbcDecAArch64, h₄.mem] using result
  · rw [h₄.gpr_of (.inl (List.mem_map.mpr ⟨_, mem_saveSlots hi, rfl⟩))]
    exact g₁ _ (savedNe i hi).1 (savedNe i hi).2

/-! ## Fewer than eleven blocks, or the batch -/

open VG.Proof.TripleDes.AArch64 (batchPre blkLen fbPub abi_of batchTaint_agree batchSat
  cbcDecFrameSat_pre)

theorem saved_cases : ∀ i < 10,
    (i < 9 ∧ Impl.Modes.AArch64.Core.savedRegs.getD i .x19 = VG.Impl.CmacTripleDes.AArch64.savedReg i) ∨
      Impl.Modes.AArch64.Core.savedRegs.getD i .x19 = .x28 := by decide

theorem saved_ne13 : ∀ i < 10, Impl.Modes.AArch64.Core.savedRegs.getD i .x19 ≠ .x13 := by decide

/-- Either path is CBC decryption and keeps the registers the modes save. -/
theorem cbcDecryptChained_wp {s₀ : State} (hp : cbcDecAArch64.pre s₀) :
    WP isa cbcDecryptChained s₀ fun s' =>
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecAArch64.post s₀ s' := by
  refine few_wp fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  obtain hp₁ : cbcDecAArch64.pre s₁ := by
    simpa only [cbcDecAArch64, batchPre, blkLen, m₁, rd₁, wr₁, g₁ .x0 (by decide), g₁ .x1 (by decide),
      g₁ .x2 (by decide), g₁ .x3 (by decide), g₁ .x4 (by decide)] using hp
  have transfer {s' : State}
      (h : (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₁.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecAArch64.post s₁ s') :
      (∀ i < 10, s'.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19) =
        s₀.gpr (Impl.Modes.AArch64.Core.savedRegs.getD i .x19)) ∧ cbcDecAArch64.post s₀ s' := by
    refine ⟨fun i hi => (h.1 i hi).trans (g₁ _ (saved_ne13 i hi)), ?_⟩
    simpa only [cbcDecAArch64, VG.Proof.TripleDes.AArch64.blocksOf, VG.Proof.TripleDes.AArch64.ivOf,
      m₁, g₁ .x0 (by decide), g₁ .x1 (by decide), g₁ .x2 (by decide), g₁ .x3 (by decide)] using h.2
  constructor
  · obtain ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, -, -, fitD, -⟩ := hp₁
    refine WP.mono (WP.gprs (cbc_wp ⟨hrd, hwr, dKV, dKD, dKS, dVD, dVS, dDS, fitD⟩) (rs := [.x28])
      (by lit_decide) (by lit_decide)) fun s' ⟨⟨post, sv⟩, o⟩ => transfer ⟨fun i hi => ?_, post⟩
    rcases saved_cases i hi with ⟨h9, e⟩ | e
    · rw [e]; exact sv i h9
    · rw [e]; exact o _ (by simp)
  · exact WP.mono (VG.Proof.TripleDes.AArch64.cbcDecryptChained_wp hp₁) fun _ h => transfer h

/-- Either path keeps the return address: the table block's, which calls
nothing and does not write it, and the batch's, which keeps it across its
calls. -/
theorem cbcDecryptChained_keeps_x30 : Modes.AArch64.KeepsReg .x30 VG.Impl.TripleDes.AArch64.Short.cbcDecryptChained := by
  refine Modes.AArch64.KeepsReg.seq (Modes.AArch64.keepsReg_of_regSafe (by decide))
    (Modes.AArch64.KeepsReg.ite (Modes.AArch64.keepsReg_of_regSafe (by lit_decide)) ?_)
  show Modes.AArch64.KeepsReg .x30 VG.Impl.TripleDes.AArch64.cbcDecryptChained
  keeps_x30

theorem cbcDecryptChained_verified :
    Verified AArch64.target cbcDecryptChained
      (Proof.TripleDes.cbcDecChainedScratchContract AArch64.abi 140) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, ⟨h₁, h₂⟩, h₃⟩ := VG.Proof.TripleDes.AArch64.WP.gprs' cbcDecryptChained_keeps_x30 (cbcDecryptChained_wp hs)
      exact ⟨t, s', he, abi_of he h₁ h₃ (by lit_decide), h₂⟩)
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) batchTaint_agree
      (by taint_decide)) (by
    sig_implies [Proof.TripleDes.cbcDecChainedScratchContract, Proof.TripleDes.cbcChainedScratchSig,
      Spec.TripleDes.cbcChainedSig, Proof.TripleDes.cbcDecChainedPost, cbcDecAArch64, batchPre, fbPub,
      AArch64.abi, AArch64.argRegs] [batchSat] using batchSat)

/-- CBC decryption with its working space on the stack. -/
theorem cbcDecryptChained_framed :
    Verified AArch64.target
      (Impl.StackScratch.AArch64.withStackScratchWiped 1120 .x4 140 cbcDecryptChained)
      (Spec.TripleDes.cbcDecryptChainedContract AArch64.abi 1120) :=
  AArch64.Verified.stackScratchWiped (sig := Spec.TripleDes.cbcChainedSig) (nm := "scratch") (e := .u64)
    (n := 140) (post := Proof.TripleDes.cbcDecChainedPost AArch64.abi.ptrBits) (wa := true) (stack := 0)
    (bytes := 1120) cbcDecryptChained_verified
    (by decide) (by decide) (by decide) (Proof.TripleDes.cbcDecChainedPostOut_local _) cbcDecFrameSat_pre

end VG.Proof.TripleDes.AArch64.Short.Cbc
