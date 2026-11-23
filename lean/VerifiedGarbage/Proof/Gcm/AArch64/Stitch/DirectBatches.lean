module

public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Steps
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
public import VerifiedGarbage.Proof.Aes.AArch64.Aese.Ctr32
public import VerifiedGarbage.Impl.Gcm.AArch64.Stitch
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ops
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Gcm.Ctr
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Weave
public import VerifiedGarbage.Proof.Framework.AArch64.InterleaveFootprints
import all Init.Data.Nat.Bitwise.Basic
public import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Ok
import VerifiedGarbage.Proof.Gcm.AArch64.Stitch.Loop
public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Tbl
public import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.Pre
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.AesGcm.AArch64.Absorb

@[expose] public section

/-! Counter mode reads plaintext at x15 while the woven GHASH reads ciphertext at x9. -/

namespace VG.Proof.Gcm.AArch64.Stitch

open VG VG.AArch64
open VG.Impl.Gcm.AArch64.Stitch
open VG.Proof.Aes.AArch64.Aese (st KeyIs rnds round_st last_st keyIs_readW getD_st exec_ldrq ctrVec_st
  vbyte_xor vbyte_readW setV_v_self setV_v_of_ne setV_setV Fr exec_addImm_w sw32)
open VG.Proof.Aes.AArch64 (keyStream)
open VG.Spec.Aes (roundKey cipher addRoundKey)
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV v_write gpr_write_self
  gpr_write_of_ne mem_write rd_write wr_write sp_write)

structure APostTo (nr o k : Nat) (s s' : State) : Prop where
  out : ∀ j < 8, ∀ t < 16, vbyte (s'.v (breg j)) t =
    keyStream nr (sch nr s) (cbk s) (16 * (k + j) + t) ^^^
      s.mem (s.gpr .x15 + BitVec.ofNat 64 (o + 16 * j) + BitVec.ofNat 64 t)
  x10 : s'.read .w .x10 = c0 s + BitVec.ofNat 32 (k + 8)
  fr : Fr [.x10, .x12] aesV s s'

theorem eor3To_run (j o : Nat) (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .x15 + BitVec.ofNat 64 (o + 16 * j)) 16)
    (ho : o + 16 * j < 65536) (ho' : (o + 16 * j) % 16 = 0) :
    runBlock isa [.ldrq P .x15 (o + 16 * j), .vop (.eor3 (breg j) (breg j) P K)] s =
      some ((s.setV P (s.mem.readW (s.gpr .x15 + BitVec.ofNat 64 (o + 16 * j)) 128)).setV (breg j)
        (s.v (breg j) ^^^ s.mem.readW (s.gpr .x15 + BitVec.ofNat 64 (o + 16 * j)) 128 ^^^ s.v K)) := by
  rw [runBlock_cons]
  rw [exec_ldrq ⟨ho', ho⟩ hin, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, isa, exec, VOp.eval, Option.map_some]
  rw [setV_v_self, setV_v_of_ne _ _ (breg_ne_P j), setV_v_of_ne _ _ (by decide : K ≠ P)]

/-- The text blocks at `x15 + o` added to the states and the last round key (in `v30`). -/
theorem fin8To_ok {o : Nat} (ho : o ≤ 128) (s : State)
    (hin : ∀ j < 8, InRegions (s.rd ++ s.wr) (s.gpr .x15 + BitVec.ofNat 64 (o + 16 * j)) 16)
    (ho16 : o % 16 = 0) :
    WP isa (.block ((List.range 8).flatMap fun j =>
        [.ldrq P .x15 (o + 16 * j), .vop (.eor3 (breg j) (breg j) P K)])) s fun s' =>
      (∀ j < 8, s'.v (breg j) = s.v (breg j) ^^^ s.mem.readW (s.gpr .x15 + BitVec.ofNat 64 (o + 16 * j)) 128 ^^^ s.v K) ∧
      Fr [] aesV s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s' =>
      (∀ j < i, s'.v (breg j) = s.v (breg j) ^^^ s.mem.readW (s.gpr .x15 + BitVec.ofNat 64 (o + 16 * j)) 128 ^^^ s.v K) ∧
      (∀ j, i ≤ j → j < 8 → s'.v (breg j) = s.v (breg j)) ∧ Fr [] aesV s s' ∧ s'.v K = s.v K)
    (fun i s₁ hi ⟨e₁, u₁, f₁, k₁⟩ => ?_) 8 (Nat.le_refl _) s
    ⟨fun _ h => absurd h (by omega_arith), fun _ _ _ => rfl, Fr.refl _ _ _, rfl⟩)
    fun s' ⟨e, _, f, _⟩ => ⟨e, f⟩
  have hin₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x15 + BitVec.ofNat 64 (o + 16 * i)) 16 := by
    rw [f₁.rd, f₁.wr, f₁.gpr _ (by decide)]; exact hin i hi
  refine WP.of_runBlock ⟨_, eor3To_run i o s₁ hin₁ (by omega_arith) (by omega_arith), ?_⟩
  have hne : ∀ j, j < 8 → j ≠ i → breg j ≠ breg i := fun j hj hji h => hji (breg_inj j hj i hi h)
  refine ⟨fun j hj => ?_, fun j hj hj8 => ?_, ?_, ?_⟩
  · by_cases hji : j = i
    · subst hji; rw [setV_v_self, u₁ j (Nat.le_refl _) hi, k₁, f₁.mem, f₁.gpr _ (by decide)]
    · rw [setV_v_of_ne _ _ (hne j (by omega_arith) hji), setV_v_of_ne _ _ (breg_ne_P j)]; exact e₁ j (by omega_arith)
  · rw [setV_v_of_ne _ _ (hne j hj8 (by omega_arith)), setV_v_of_ne _ _ (breg_ne_P j), u₁ j (by omega_arith) hj8]
  · refine f₁.trans ⟨fun _ _ => rfl, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    rw [setV_v_of_ne _ _ fun h => hr (by rw [h]; exact breg_mem i), setV_v_of_ne _ _ fun h => hr (by rw [h]; decide)]
  · rw [setV_v_of_ne _ _ (breg_ne_K i).symm, setV_v_of_ne _ _ (by decide : K ≠ P), k₁]

theorem aesPartTo_ok {nr o k : Nat} {s : State} (hp : APre nr o k s) (hinp : ∀ j < 8, InRegions (s.rd ++ s.wr) (s.gpr .x15 + BitVec.ofNat 64 (o + 16 * j)) 16)
    (ho16 : o % 16 = 0) :
    WP isa (.block (aesPart nr o .x15)) s (APostTo nr o k s) := by
  have hR := hp.rounds
  unfold aesPart
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ctrs_ok hp) fun s₁ ⟨e₁, f₁⟩ => ?_
  -- The counter blocks, as AES states.
  let x : Nat → Spec.Aes.State := fun j => Proof.Aes.ctrState (cbk s) (k + j)
  have hx : ∀ j < 8, st (cvec s k j) = x j := fun j _ => by
    show _ = Proof.Aes.ctrState _ _
    rw [cvec, BitVec.add_assoc, ← BitVec.ofNat_add, c0, cbk, cbA, ← ctrVec_st, BitVec.add_zero]
  have hI₁ : RI (sch nr s) x 0 s₁ := fun j hj => by rw [e₁ j hj, hx j hj]; rfl
  refine WP.mono (rnds_ok hp f₁ hI₁ (nr - 1) (by omega_arith)) fun s₂ ⟨e₂, f₂⟩ => ?_
  -- The last round.
  have g₂ : s₂.gpr .x21 = s.gpr .x21 := f₂.gpr _ (by decide)
  have hin : ∀ r ≤ nr, InRegions (s₂.rd ++ s₂.wr) (s₂.gpr .x21 + BitVec.ofNat 64 (16 * r)) 16 :=
    fun r hr => by rw [f₂.rd, f₂.wr, g₂]; exact hp.keys r hr
  unfold lastRnd
  rw [WP.block_append_iff, WP.block_cons_iff]
  refine ⟨_, exec_ldrq (by omega_arith) (hin (nr - 1) (by omega_arith)), ?_⟩
  generalize hK₁ : s₂.mem.readW (s₂.gpr .x21 + BitVec.ofNat 64 (16 * (nr - 1))) 128 = K₁
  refine WP.mono (aese8_ok _) fun s₃ ⟨e₃, f₃, _⟩ => ?_
  rw [WP.block_cons_iff]
  have hin₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .x21 + BitVec.ofNat 64 (16 * nr)) 16 := by
    rw [f₃.rd, f₃.wr, f₃.gpr _ (by decide), rd_setV, wr_setV, gpr_setV]
    exact hin nr (Nat.le_refl _)
  refine ⟨_, exec_ldrq (by omega_arith) hin₃, ?_⟩
  generalize hK₂ : s₃.mem.readW (s₃.gpr .x21 + BitVec.ofNat 64 (16 * nr)) 128 = K₂
  have g₃ : ∀ r, s₃.gpr r = s₂.gpr r := fun r => by rw [f₃.gpr r (by simp)]; rfl
  have m₃ : s₃.mem = s.mem := by rw [f₃.mem, mem_setV, f₂.mem]
  have hin₄ : ∀ j < 8, InRegions ((s₃.setV K K₂).rd ++ (s₃.setV K K₂).wr)
      ((s₃.setV K K₂).gpr .x15 + BitVec.ofNat 64 (o + 16 * j)) 16 := fun j hj => by
    rw [rd_setV, wr_setV, gpr_setV, f₃.rd, f₃.wr, g₃, rd_setV, wr_setV, f₂.rd,
      f₂.wr, f₂.gpr _ (by decide)]
    exact hinp j hj
  refine WP.mono (fin8To_ok hp.o_le _ hin₄ ho16) fun s₄ ⟨e₄, f₄⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨_, exec_addImm_w (imm := 8) (by decide), WP.block_nil ?_⟩
  -- The keys, and the last round of each block.
  have hk₁ : KeyIs K₁ (roundKey (sch nr s) (nr - 1)) := by
    rw [← hK₁, f₂.mem, g₂]; exact keyIs_readW _ _ (by omega_arith)
  have hk₂ : KeyIs K₂ (roundKey (sch nr s) nr) := by
    rw [← hK₂, m₃, g₃, g₂]; exact keyIs_readW _ _ (by omega_arith)
  have g₁₅ : s₃.gpr .x15 = s.gpr .x15 := by rw [g₃, f₂.gpr _ (by decide)]
  refine ⟨fun j hj t ht => ?_, ?_, ?_⟩
  · rw [v_write, e₄ j hj, v_setV_of_ne _ _ (breg_ne_K j), e₃ j hj, v_setV_of_ne _ _ (breg_ne_K j),
      v_setV_self, v_setV_self, mem_setV, gpr_setV, m₃, g₁₅,
      show ∀ A M C : BitVec 128, A ^^^ M ^^^ C = (A ^^^ C) ^^^ M from fun A M C => by ac_rfl, vbyte_xor,
      vbyte_readW _ _ ht, keyStream_byte ht, ← getD_st _ ht,
      last_st hk₁ hk₂ (e₂ j hj)]
  · have hx := hp.x10
    have g₁₀ : s₄.gpr .x10 = s.gpr .x10 := by
      rw [f₄.gpr _ (by simp), gpr_setV, g₃, f₂.gpr _ (by decide)]
    simp only [State.read] at hx ⊢
    rw [gpr_write_self, sw32, g₁₀, hx, BitVec.add_assoc, ← BitVec.ofNat_add]
  · have f₄' : Fr [] aesV s₃ s₄ := (fr_setV _ _ (by decide)).trans f₄
    have f₃' : Fr [] aesV s₂ s₃ := (fr_setV _ _ (by decide)).trans f₃
    refine ((f₂.trans (fr_widen (f₃'.trans f₄') _)).mono (fun r h => List.mem_cons_of_mem _ h)
      (fun _ h => h)).trans ⟨fun r hr => ?_, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact gpr_write_of_ne _ _ _ hr.1

end VG.Proof.Gcm.AArch64.Stitch

/-! Independence for the gather seal loop, with separate plaintext and ciphertext pointers. -/

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.Impl.Gcm.AArch64.Stitch

theorem partsTo_check : ∀ nr ∈ [10, 12, 14], ∀ o ∈ [0, 128],
    ((fps.blockFp (aesPart nr o .x15)).bind fun A => (fps.blockFp ghPart).map fun B => fps.indep A B) = some true := by
  decide +kernel

theorem partsTo_indeps {nr o : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) (ho : o = 0 ∨ o = 128) :
    VG.Interleave.Indeps isa fps.Inv (aesPart nr o .x15) ghPart :=
  fps.indeps_of_check (partsTo_check nr (by rcases hnr with rfl | rfl | rfl <;> decide) o
    (by rcases ho with rfl | rfl <;> decide))

/-- The parts, woven, run as `aesPart` and then `ghPart`. -/
theorem partsTo_ok {nr o : Nat} (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) (ho : o = 0 ∨ o = 128) {s : State}
    {Q : State → Prop} (h : WP isa (.block (aesPart nr o .x15)) s fun t => WP isa (.block ghPart) t Q) :
    WP isa (.block (parts nr o .x15)) s Q := by
  unfold parts
  refine VG.Interleave.WP.weaveG (P := fps.Inv) ?_ trivial ?_
  · rw [fuse_flatten, flatten_singles]; exact partsTo_indeps hnr ho
  · rw [fuse_flatten, flatten_singles]; exact h

end VG.Proof.Gcm.AArch64.Stitch

/-! Source and destination invariants for the pipelined gather kernel. -/

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV v_write
  gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.Aes.AArch64 (DataInv DataInvM dataInvM_self dataInvM_frame dataInvM_store1 ctr32_of_dataInvM keyStream)
open VG.Proof.Aes.AArch64.Aese (Fr vbyte_readW inRegions_wr exec_strq)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly rev64b_read)
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom ctr32)
open VG.Impl.Gcm.AArch64.Stitch


/-- Keep the output and its bounds as in the ordinary sealing kernel.
The input may overlap other read-only arguments, but is disjoint from the output. -/
structure SealToPre (s : State) extends KPre s where
  src_in : InRegions (s.rd ++ s.wr) (s.gpr .x15) (128 * nb s)
  src_dst : (⟨s.gpr .x15, 128 * nb s⟩ : Region).Disjoint (dR s)
  wrap_src : (s.gpr .x15).toNat + 128 * nb s ≤ 2 ^ 64

/-- Reindex the same buffers for the generic out-of-place store lemma. -/
def storeEntry (s : State) : State :=
  { s with gpr := fun r => if r = .x23 then s.gpr .x15 else if r = .x15 then dp s else s.gpr r }

theorem SealToPre.stores {s : State} (hp : SealToPre s) : KPreM (storeEntry s) true where
  rounds := hp.rounds
  nb1 := hp.nb1
  k_in := hp.k_in
  y_in := hp.y_in
  c_in := hp.c_in
  d_in := hp.src_in
  o_in := hp.d_in
  t_in := hp.t_in
  o_k := hp.d_k
  o_y := hp.d_y
  o_c := hp.d_c
  o_t := hp.d_t
  d_o _ := hp.src_dst
  y_c := hp.y_c
  wrap_d := hp.wrap_src
  wrap_o := hp.wrap_d
  wrap_k := hp.wrap_k
  wrap_t := hp.wrap_t
  wrap_s := hp.wrap_s
  tbl := hp.tbl

/-- Batch ciphertext derived from the plaintext supplied on entry. -/
abbrev cipherBlock (s : State) (i : Nat) : Block := blockC (storeEntry s) i

structure SealInv (s₀ : State) (c h : Nat) (s : State) : Prop where
  le : c ≤ nb s₀
  x9 : s.gpr .x9 = dp s₀ + BitVec.ofNat 64 (128 * h)
  x10 : s.read .w .x10 = ctr0 s₀ + BitVec.ofNat 32 (8 * c)
  x11 : s.gpr .x11 = BitVec.ofNat 64 (nb s₀ - c)
  x15 : s.gpr .x15 = s₀.gpr .x15 + BitVec.ofNat 64 (128 * h)
  gpr : ∀ r, r ∉ kRegsT true → s.gpr r = s₀.gpr r
  y : s.v Y = ext8 (yh s₀ (cipherBlock s₀) (8 * h)) (yh s₀ (cipherBlock s₀) (8 * h))
  cr : s.v C = ofVDwords Impl.Gcm.AArch64.Pmull.poly Impl.Gcm.AArch64.Pmull.poly
  data : DataInvM s₀.mem s.mem (s₀.gpr .x15) (dp s₀) (8 * nb s₀) (8 * c) (kst s₀)
  frame : Frame [dR s₀] s₀.mem s.mem
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem ciphertext_of_dataInvM {m₀ m : Mem} {D O : Addr} {n k R : Nat} {w : List Byte} {icb : Block}
    (h : DataInvM m₀ m D O n k (keyStream R w icb)) {i : Nat} (hi : i < k) (hk : k ≤ n) :
    blockAt m (O + BitVec.ofNat 64 (16 * i)) =
      blockAt m₀ (D + BitVec.ofNat 64 (16 * i)) ^^^ aesWith R w (Nat.repeat inc32 i icb) := by
  refine Proof.Aes.block_ext fun t ht => ?_
  rw [Proof.Aes.toBytes_xor _ _ ht, Proof.Aes.toBytes_blockAt _ _ ht, Proof.Aes.toBytes_blockAt _ _ ht,
    BitVec.add_assoc, ← BitVec.ofNat_add, h _ (by omega_using [hi, hk, ht]), ite_eq_left (by omega_using [hi, ht])]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  refine congrArg (_ ^^^ ·) ?_
  unfold Spec.Gcm.aesWith
  rw [Proof.Aes.toBytes_ofBytes (by simp) ht, keyStream, show (16 * i + t) / 16 = i by omega_using [ht],
    show (16 * i + t) % 16 = t by omega_using [ht], Proof.Aes.getD_eq _ ht, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem ht, Option.getD_some]
  rfl

theorem aesToStep {s₀ : State} (hp : SealToPre s₀) {c h o : Nat} {s : State}
    (hI : SealInv s₀ c h s) (hc : c < nb s₀) (ho : 128 * h + o = 128 * c) (ho' : o ≤ 128) (ho16 : o % 16 = 0) :
    WP isa (.block (aesPart (rounds s₀) o .x15)) s fun t =>
      (∀ j < 8, ∀ tt < 16, vbyte (t.v (breg j)) tt =
        kst s₀ (16 * (8 * c + j) + tt) ^^^ s₀.mem (s₀.gpr .x15 + BitVec.ofNat 64 (16 * (8 * c + j) + tt))) ∧
      t.read .w .x10 = ctr0 s₀ + BitVec.ofNat 32 (8 * (c + 1)) ∧ Fr [.x10, .x12] aesV s t := by
  have hn := hp.toKPre.toM.n16
  have hR := hp.rounds
  have g21 : s.gpr .x21 = kc s₀ := hI.gpr _ (notMem_kRegsT _ (by decide))
  have g20 : s.gpr .x20 = stp s₀ := hI.gpr _ (notMem_kRegsT _ (by decide))
  have rdwr : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hI.rd, hI.wr]
  have hx9 : ∀ j, s.gpr .x9 + BitVec.ofNat 64 (o + 16 * j) = dp s₀ + BitVec.ofNat 64 (16 * (8 * c + j)) :=
    fun j => by rw [hI.x9, Offset.add_add_eq _ (show 128 * h + (o + 16 * j) = 16 * (8 * c + j) by omega_arith)]
  have hx15 : ∀ j, s.gpr .x15 + BitVec.ofNat 64 (o + 16 * j) = s₀.gpr .x15 + BitVec.ofNat 64 (16 * (8 * c + j)) :=
    fun j => by rw [hI.x15, Offset.add_add_eq _ (show 128 * h + (o + 16 * j) = 16 * (8 * c + j) by omega_arith)]
  have hcb : cbk s = icb s₀ := by rw [cbk, cbA, g20]; exact hp.toKPre.toM.c_frame hI.frame
  have hA : APre (rounds s₀) o (8 * c) s := {
    rounds := hR
    o_le := ho'
    keys := fun r hr => by
      rw [rdwr, kp, g21]; exact CallLay.inRegions_sub hp.k_in (by omega_arith) (by omega_arith)
    ctr := by
      rw [rdwr, cbA, g20, BitVec.add_zero]
      exact inRegions_wr hp.c_in
    data := fun j hj => by
      rw [rdwr, hx9]
      exact CallLay.inRegions_sub (inRegions_wr hp.d_in) (by omega_arith) (by omega_arith)
    x10 := by rw [hI.x10, c0, hcb] }
  refine WP.mono (aesPartTo_ok hA (fun j hj => by rw [rdwr, hx15]; exact CallLay.inRegions_sub hp.src_in (by omega_arith) (by omega_arith)) ho16) fun t ⟨out, x10, fr⟩ => ⟨fun j hj tt htt => ?_, ?_, fr⟩
  · rw [out j hj tt htt, sch, kp, g21, hp.toKPre.toM.sch_frame hI.frame, hcb, hx15, Offset.add_add]
    rw [hI.frame.bytes (R := ⟨s₀.gpr .x15, 128 * nb s₀⟩) (by simpa using hp.src_dst) (by dsimp only; omega_arith) (by dsimp only; omega_arith)]
  · rw [x10, c0, hcb, show 8 * c + 8 = 8 * (c + 1) by omega_arith]


end VG.Proof.Gcm.AArch64.Stitch

/-! Encrypt one batch while hashing ciphertext at the separate output pointer. -/

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV v_write
  gpr_write gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.Aes.AArch64 (DataInv keyStream)
open VG.Proof.Aes.AArch64.Aese (Fr vbyte_readW inRegions_wr exec_strq)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly rev64b_read)
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom ctr32)
open VG.Impl.Gcm.AArch64.Stitch

theorem encToBody_ok {s₀ : State} (hp : SealToPre s₀) (gh : Gh8Ok) {c h o : Nat}
    (hc : c < nb s₀) (hh : h < nb s₀) (hho : 128 * h + o = 128 * c) (ho : o = 0 ∨ o = 128)
    {s : State} (hI : SealInv s₀ c h s)
    (hhb : ∀ j < 8, blockAt s.mem (dp s₀ + BitVec.ofNat 64 (16 * (8 * h + j))) = cipherBlock s₀ (8 * h + j)) :
    WP isa (.block (parts (rounds s₀) o .x15 ++ stores o ++ adv true)) s
      (SealInv s₀ (c + 1) (h + 1)) := by
  have ho' : o ≤ 128 := by omega_using [ho]
  have ho16 : o % 16 = 0 := by omega_using [hho]
  have hout : s.gpr .x9 + BitVec.ofNat 64 o = dp s₀ + BitVec.ofNat 64 (128 * c) := by
    rw [hI.x9, Offset.add_add_eq _ hho]
  rw [List.append_assoc, WP.block_append_iff]
  refine partsTo_ok hp.rounds ho ?_
  refine WP.mono (aesToStep hp hI hc hho ho' ho16) fun t ⟨hv, x10t, frt⟩ => ?_
  have gt : ∀ r, r ≠ .x10 → r ≠ .x12 → t.gpr r = s.gpr r := fun r h1 h2 => frt.gpr r (by simp [h1, h2])
  refine WP.mono (ghStep hp.toKPre.toM gh (hb := cipherBlock s₀) (t := t) (by rw [frt.v _ (by decide), hI.y])
    (by rw [frt.v _ (by decide), hI.cr]) (by rw [gt _ (by decide) (by decide), hI.x9]) hh
    (by rw [gt _ (by decide) (by decide), hI.gpr _ (notMem_kRegsT _ (by decide))])
    (by rw [frt.rd, frt.wr, hI.rd, hI.wr]) (by rw [frt.mem]; exact hI.frame)
    (fun j hj => by rw [frt.mem]; exact hhb j hj)) fun u ⟨hy, ou⟩ => ?_
  rw [WP.block_append_iff]
  have gu : ∀ r, r ≠ .x10 → r ≠ .x12 → u.gpr r = s.gpr r := fun r h1 h2 => by rw [ou.gpr, gt r h1 h2]
  refine WP.mono (stores_ok hp.stores hc ho' ho16 u .x9 (by rw [gu _ (by decide) (by decide), hout]; rfl)
      (by rw [ou.mem, frt.mem]; exact hI.data) (by rw [ou.wr, frt.wr, hI.wr]; rfl)
    (fun j hj tt htt => by rw [ou.v _ (by unfold breg; split <;> decide)]; exact hv j hj tt htt))
    fun u₁ ⟨d₁, f₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_
  rw [adv, WP.block_append_iff]
  refine WP.mono (advO_ok («to» := true) u₁) fun u₂ ⟨x15₂, g₂, v₂, m₂, sp₂, rd₂, wr₂⟩ => ?_
  have g₂' : ∀ r, r ≠ .x15 → u₂.gpr r = u₁.gpr r := fun r h => g₂ r fun _ => h
  refine WP.mono (adv_ok (h := h) hc (by rw [g₂' _ (by decide), g₁, gu _ (by decide) (by decide), hI.x9])
    (by rw [g₂' _ (by decide), g₁, gu _ (by decide) (by decide), hI.x11]))
    fun u' ⟨x9', x11', g', v', m', sp', rd', wr'⟩ => ?_
  have gall : ∀ r, r ≠ .x9 → r ≠ .x11 → (true = true → r ≠ .x15) → u'.gpr r = u.gpr r :=
    fun r h9 h11 h15 => by rw [g' r h9 h11, g₂ r h15, g₁]
  refine ⟨by omega_using [hc], x9', ?_, x11', ?_, fun r hr => ?_, ?_, ?_, by rw [m', m₂]; exact d₁, ?_, ?_, ?_, ?_⟩
  · simp only [State.read] at x10t ⊢
    rw [gall _ (by decide) (by decide) (fun _ => by decide), ou.gpr]; exact x10t
  · rw [g' _ (by decide) (by decide), x15₂ rfl, g₁, gu _ (by decide) (by decide), hI.x15,
      Offset.add_add_eq _ (show 128 * h + 128 = 128 * (h + 1) by omega_using [])]
  · obtain ⟨hrk, hr15⟩ := kRegsT_not hr
    simp only [kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hrk
    rw [gall r hrk.1 hrk.2.2.1 hr15, gu r hrk.2.1 hrk.2.2.2.1, hI.gpr r hr]
  · rw [v', v₂, v₁, hy]
  · rw [v', v₂, v₁, ou.v C (by decide), frt.v C (by decide), hI.cr]
  · rw [m', m₂]
    have : s.mem = u.mem := by rw [ou.mem, frt.mem]
    exact hI.frame.trans (this ▸ f₁)
  · rw [sp', sp₂, sp₁, ou.sp, frt.sp, hI.sp]
  · rw [rd', rd₂, rd₁, ou.rd, frt.rd, hI.rd]
  · rw [wr', wr₂, wr₁, ou.wr, frt.wr, hI.wr]

end VG.Proof.Gcm.AArch64.Stitch

/-! The full gather encryption loop, including its first and last pipeline batches. -/

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV v_write
  gpr_write gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.Aes.AArch64 (DataInv DataInvM dataInvM_self dataInvM_frame dataInvM_store1 ctr32_of_dataInvM keyStream)
open VG.Proof.Aes.AArch64.Aese (Fr vbyte_readW inRegions_wr exec_strq eval_zero eval_nonzero sw32)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly rev64b_read)
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom ctr32)
open VG.Impl.Gcm.AArch64.Stitch

theorem encToLoop_ok {s₀ : State} (hp : SealToPre s₀) (gh : Gh8Ok) {s : State}
    (hI : SealInv s₀ 0 0 s) :
    WP isa (encToLoop (rounds s₀)) s (SealInv s₀ (nb s₀) (nb s₀)) := by
  have hn := hp.toKPre.toM.n16
  have h1 := hp.nb1
  -- The batch at `x9 + 16 (8 h + j)`, once encrypted.
  have hct : ∀ {c h : Nat} {s : State}, SealInv s₀ c h s → h < c →
      ∀ j < 8, blockAt s.mem (dp s₀ + BitVec.ofNat 64 (16 * (8 * h + j))) = cipherBlock s₀ (8 * h + j) :=
    fun hI hhc j hj => ciphertext_of_dataInvM hI.data (by omega_arith) (by have := hI.le; omega_arith)
  have step_eq (xs : List Instr) : xs ++ [.addImm .x .x15 .x15 128, .addImm .x .x9 .x9 128] ++
      [.subImm .x .x11 .x11 1] = xs ++ adv true := by rw [List.append_assoc]; rfl
  simp only [encToLoop, step_eq]
  refine WP.seq ?_
  -- The first batch.
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (aesToStep hp hI (by omega_arith) (show 128 * 0 + 0 = 128 * 0 by rfl) (by decide) (by decide))
    fun t ⟨hv, x10t, frt⟩ => ?_
  have gt : ∀ r, r ≠ .x10 → r ≠ .x12 → t.gpr r = s.gpr r := fun r h1 h2 => frt.gpr r (by simp [h1, h2])
  refine WP.mono (stores_ok hp.stores (c := 0) (show 0 < nb s₀ from h1) (by decide) (by decide) t .x9
    (by rw [gt _ (by decide) (by decide), hI.x9, BitVec.add_zero]; rfl) (by rw [frt.mem]; exact hI.data)
    (by rw [frt.wr, hI.wr]; rfl) hv) fun u ⟨d₁, f₁, g₁, v₁, sp₁, rd₁, wr₁⟩ => ?_
  rw [WP.block_cons_iff]
  refine ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil ?_⟩
  have hI₁ : SealInv s₀ 1 0 (u.write .x .x11 (u.read .x .x11 - BitVec.ofNat 64 1)) := {
    le := h1
    x9 := by rw [gpr_write_of_ne _ _ _ (by decide), g₁, gt _ (by decide) (by decide), hI.x9]
    x10 := by
      simp only [State.read] at x10t ⊢
      rw [gpr_write_of_ne _ _ _ (by decide), g₁]; exact x10t
    x11 := by
      simp only [gpr_write_self, State.read, BitVec.setWidth_eq]
      rw [g₁, gt .x11 (by decide) (by decide), hI.x11, Nat.sub_zero, Offset.ofNat_sub_ofNat (by omega_arith)]
    x15 := by rw [gpr_write_of_ne _ _ _ (by decide), g₁, gt _ (by decide) (by decide), hI.x15]
    gpr := fun r hr => by
      have hk := (kRegsT_not hr).1
      simp only [kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      rw [gpr_write_of_ne _ _ _ hk.2.2.1, g₁, gt r hk.2.1 hk.2.2.2.1, hI.gpr r hr]
    y := by rw [v_write, v₁, frt.v _ (by decide), hI.y]
    cr := by rw [v_write, v₁, frt.v _ (by decide), hI.cr]
    data := by rw [mem_write]; exact d₁
    frame := by rw [mem_write]; exact hI.frame.trans (frt.mem ▸ f₁)
    sp := by rw [sp_write, sp₁, frt.sp, hI.sp]
    rd := by rw [rd_write, rd₁, frt.rd, hI.rd]
    wr := by rw [wr_write, wr₁, frt.wr, hI.wr] }
  -- The loop, then the last batch hashed.
  refine WP.seq (WP.mono (Q := SealInv s₀ (nb s₀) (nb s₀ - 1)) ?_ fun s₂ hI₂ => ?_)
  · refine WP.ite (decide (nb s₀ - 1 = 0)) (eval_zero hI₁.x11 (by omega_arith)) (fun h => ?_) (fun h => ?_)
    · have : nb s₀ = 1 := by simp at h; omega_arith
      exact WP.block_nil (by rw [this]; exact hI₁)
    · let I : Nat → State → Prop := fun m s => ∃ h, m = nb s₀ - (h + 1) ∧ h + 1 < nb s₀ ∧
          SealInv s₀ (h + 1) h s
      have hstep : ∀ m s, I m s → WP isa (.block (parts (rounds s₀) 128 .x15 ++ stores 128 ++ adv true)) s (fun s' =>
          (AArch64.eval (.nonzero .x .x11) s' = some false ∧ SealInv s₀ (nb s₀) (nb s₀ - 1) s') ∨
          (AArch64.eval (.nonzero .x .x11) s' = some true ∧ ∃ m' < m, I m' s')) := by
        rintro m s ⟨h, rfl, hh, hI⟩
        refine WP.mono (encToBody_ok hp gh (by omega_arith) (by omega_arith) (by omega_arith) (.inr rfl) hI (hct hI (by omega_arith)))
          fun s' hI' => ?_
        rw [eval_nonzero hI'.x11 (by omega_arith)]
        by_cases hl : nb s₀ - (h + 1 + 1) = 0
        · have e : h + 1 + 1 = nb s₀ := by omega_arith
          exact .inl ⟨by simp [hl], by rw [← e, show h + 1 + 1 - 1 = h + 1 by omega_arith]; exact hI'⟩
        · exact .inr ⟨by simp [hl], nb s₀ - (h + 1 + 1), by omega_arith, h + 1, rfl, by omega_arith, hI'⟩
      exact WP.loop (M := isa) I hstep _ _ ⟨0, rfl, by simp at h; omega_arith, hI₁⟩
  · rw [WP.block_append_iff]
    refine WP.mono (ghStep hp.toKPre.toM gh (hb := cipherBlock s₀) (h := nb s₀ - 1) hI₂.y hI₂.cr hI₂.x9 (by omega_arith)
      (hI₂.gpr _ (notMem_kRegsT _ (by decide))) (by rw [hI₂.rd, hI₂.wr]) hI₂.frame (hct hI₂ (by omega_arith))) fun u ⟨hy, ou⟩ => ?_
    rw [WP.block_cons_iff]
    refine ⟨_, exec_addImm_x (imm := 128) (by decide), ?_⟩
    rw [WP.block_cons_iff]
    refine ⟨_, exec_addImm_x (imm := 128) (by decide), WP.block_nil ?_⟩
    have e : nb s₀ - 1 + 1 = nb s₀ := by omega_arith
    exact {
      le := Nat.le_refl _
      x9 := by
        simp only [gpr_write_self, State.read, BitVec.setWidth_eq, gpr_write_of_ne _ _ _ (show Reg.x9 ≠ Reg.x15 by decide), ou.gpr, hI₂.x9]
        rw [Offset.add_add_eq _ (show 128 * (nb s₀ - 1) + 128 = 128 * nb s₀ by omega_arith)]
      x10 := by
        simp only [State.read, gpr_write_of_ne _ _ _ (show Reg.x10 ≠ Reg.x9 by decide), gpr_write_of_ne _ _ _ (show Reg.x10 ≠ Reg.x15 by decide), ou.gpr]; exact hI₂.x10
      x11 := by rw [gpr_write_of_ne _ _ _ (by decide), gpr_write_of_ne _ _ _ (show Reg.x11 ≠ Reg.x15 by decide), ou.gpr, hI₂.x11]
      x15 := by
        simp only [gpr_write_of_ne _ _ _ (show Reg.x15 ≠ Reg.x9 by decide), gpr_write_self, State.read,
          BitVec.setWidth_eq, ou.gpr, hI₂.x15]
        rw [Offset.add_add_eq _ (show 128 * (nb s₀ - 1) + 128 = 128 * nb s₀ by omega_arith)]
      gpr := fun r hr => by
        rw [gpr_write_of_ne _ _ _ (fun h => hr (by simp [h, kRegsT, cond, kRegs])), gpr_write_of_ne _ _ _ ((kRegsT_not hr).2 rfl), ou.gpr, hI₂.gpr r hr]
      y := by rw [v_write, v_write, hy, e]
      cr := by rw [v_write, v_write, ou.v C (by decide), hI₂.cr]
      data := by rw [mem_write, mem_write, ou.mem]; exact hI₂.data
      frame := by rw [mem_write, mem_write, ou.mem]; exact hI₂.frame
      sp := by rw [sp_write, sp_write, ou.sp, hI₂.sp]
      rd := by rw [rd_write, rd_write, ou.rd, hI₂.rd]
      wr := by rw [wr_write, wr_write, ou.wr, hI₂.wr] }

end VG.Proof.Gcm.AArch64.Stitch

/-! Full counter, ciphertext, pointer, frame and running-GHASH postconditions for gather sealing. -/

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64
open VG.AArch64.RegUpd (v_setV_self v_setV_of_ne gpr_setV mem_setV rd_setV wr_setV sp_setV v_write
  gpr_write gpr_write_self gpr_write_of_ne mem_write rd_write wr_write sp_write)
open VG.Proof.Aes.AArch64 (DataInv DataInvM dataInvM_self dataInvM_frame dataInvM_store1 ctr32_of_dataInvM keyStream)
open VG.Proof.Aes.AArch64.Aese (sw32)
open VG.Proof.Gcm.AArch64.Pmull (ext8 VOnly blockAt_store ext8_ext8)
open VG.Spec.Gcm (Block blockAt blocksAt inc32 aesWith ghashFrom ctr32)
open VG.Impl.Gcm.AArch64.Stitch


/-- The in-place setup has only initialized the counters and hash; neither
buffer has been read or written yet. -/
theorem sealInv_start {s₀ s : State} (h : LInv s₀ false (cipherBlock s₀) 0 0 s) :
    SealInv s₀ 0 0 s where
  le := h.le
  x9 := h.x9
  x10 := h.x10
  x11 := h.x11
  x15 := by simpa using h.gpr .x15 (by decide)
  gpr r hr := h.gpr r (kRegsT_not hr).1
  y := h.y
  cr := h.cr
  data i hi := by simpa using h.data i hi
  frame := h.frame
  sp := h.sp
  rd := h.rd
  wr := h.wr

/-- The output needed by the next fragment: the ciphertext, running hash
over it, counter and both next byte pointers. -/
structure SealToPost (s₀ s : State) : Prop where
  data : blocksAt s.mem (dp s₀) (8 * nb s₀) =
    ctr32 (ciph s₀) (icb s₀) (blocksAt s₀.mem (s₀.gpr .x15) (8 * nb s₀))
  ctr : blockAt s.mem (stp s₀ + BitVec.ofNat 64 48) = Nat.repeat inc32 (8 * nb s₀) (icb s₀)
  y : blockAt s.mem (stp s₀ + BitVec.ofNat 64 16) = ghashFrom (hk s₀) (y₀ s₀) (blocksAt s.mem (dp s₀) (8 * nb s₀))
  dst : s.gpr .x9 = dp s₀ + BitVec.ofNat 64 (128 * nb s₀)
  src : s.gpr .x15 = s₀.gpr .x15 + BitVec.ofNat 64 (128 * nb s₀)
  frame : Frame [yR s₀, cR s₀, dR s₀] s₀.mem s.mem
  gpr : ∀ r, r ∉ kRegsT true → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

private structure Finished (s₀ : State) (s : State) : Prop where
  y : blockAt s.mem (stp s₀ + BitVec.ofNat 64 16) = yh s₀ (cipherBlock s₀) (8 * nb s₀)
  ctr : blockAt s.mem (stp s₀ + BitVec.ofNat 64 48) = Nat.repeat inc32 (8 * nb s₀) (icb s₀)
  data : DataInvM s₀.mem s.mem (s₀.gpr .x15) (dp s₀) (8 * nb s₀) (8 * nb s₀) (kst s₀)
  dst : s.gpr .x9 = dp s₀ + BitVec.ofNat 64 (128 * nb s₀)
  src : s.gpr .x15 = s₀.gpr .x15 + BitVec.ofNat 64 (128 * nb s₀)
  frame : Frame [yR s₀, cR s₀, dR s₀] s₀.mem s.mem
  gpr : ∀ r, r ∉ kRegsT true → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

private theorem finishTo_ok {s₀ : State} (hp : SealToPre s₀) {s : State}
    (hI : SealInv s₀ (nb s₀) (nb s₀) s) : WP isa (.block finish) s (Finished s₀) := by
  have hn := hp.toKPre.toM.n16
  have hs := hp.wrap_s
  have g20 : s.gpr .x20 = stp s₀ := hI.gpr _ (notMem_kRegsT _ (by decide))
  have e60 : stp s₀ + BitVec.ofNat 64 60 = stp s₀ + BitVec.ofNat 64 48 + BitVec.ofNat 64 12 := by
    rw [Offset.add_add]
  have hy : InRegions s.wr (s.gpr .x20 + BitVec.ofNat 64 16) 16 := by rw [hI.wr, g20]; exact hp.y_in
  have hc : InRegions s.wr (s.gpr .x20 + BitVec.ofNat 64 60) 4 := by
    rw [hI.wr, g20, e60]
    exact CallLay.inRegions_sub hp.c_in (by omega_using []) (by omega_using [])
  rw [finish, WP.block_cons_iff]
  refine ⟨_, Pmull.exec_rev64b Y Y _, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, Pmull.exec_strq (t := Y) (off := 16) (by decide) (by decide)
    (by simpa only [wr_setV, gpr_setV] using hy), ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_rev32, ?_⟩
  rw [WP.block_cons_iff]
  refine ⟨_, exec_str_w (off := 60) (by decide) (by
    simpa only [wr_write, gpr_write_of_ne _ _ _ (show Reg.x20 ≠ Reg.x12 by decide), wr_setV, gpr_setV] using hc),
    WP.block_nil ?_⟩
  simp only [gpr_write_of_ne _ _ _ (show Reg.x20 ≠ Reg.x12 by decide), gpr_setV, gpr_write_self, g20,
    v_setV_self, mem_setV, mem_write, State.read, sw32, e60]
  have hx10 : BitVec.setWidth Size.w.bits (s.gpr .x10) = ctr0 s₀ + BitVec.ofNat 32 (8 * nb s₀) := by
    have := hI.x10; simp only [State.read] at this; exact this
  rw [hx10]
  generalize hm₁ : s.mem.write (stp s₀ + BitVec.ofNat 64 16) 16 (VRevOp.eval .rev64b (s.v Y)) = m₁
  -- `Y`.
  have fy : Frame [yR s₀] s.mem m₁ := by
    rw [← hm₁]; exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have hy₁ : blockAt m₁ (stp s₀ + BitVec.ofNat 64 16) = yh s₀ (cipherBlock s₀) (8 * nb s₀) := by
    rw [← hm₁, blockAt_store, hI.y, ext8_ext8]
  -- The counter block, apart from `Y` and the data.
  have hcb : ∀ k < 16, m₁ (stp s₀ + BitVec.ofNat 64 48 + BitVec.ofNat 64 k) =
      s₀.mem (stp s₀ + BitVec.ofNat 64 48 + BitVec.ofNat 64 k) := fun k hk => by
    rw [fy.bytes (R := cR s₀) (by simp only [List.mem_singleton, forall_eq]; exact hp.y_c.symm)
      (by show (16 : Nat) ≤ 2 ^ 64; decide) hk]
    exact hI.frame.bytes (R := cR s₀) (by simp only [List.mem_singleton, forall_eq]; exact hp.d_c.symm)
      (by show (16 : Nat) ≤ 2 ^ 64; decide) hk
  have hcb₁ : blockAt m₁ (stp s₀ + BitVec.ofNat 64 48) = icb s₀ :=
    Proof.Gcm.blockAt_congr fun k hk => hcb k hk
  have hlo : rev32 (m₁.readW (stp s₀ + BitVec.ofNat 64 48 + BitVec.ofNat 64 12) 32) = ctr0 s₀ := by
    rw [Proof.Aes.AArch64.icb_lo, hcb₁]
  refine ⟨?_, ?_, ?_, hI.x9, hI.x15, ?_, fun r hr => ?_, hI.sp, hI.rd, hI.wr⟩
  · -- `Y`, apart from the counter word.
    dsimp only
    rw [← hy₁]
    refine Proof.Gcm.blockAt_congr fun k hk => ?_
    exact ((Frame.refl [⟨stp s₀ + BitVec.ofNat 64 48 + BitVec.ofNat 64 12, 4⟩] m₁).writeW
      (List.mem_singleton_self _) _ (Region.contains_self _ _)).bytes (R := yR s₀)
      (by simp only [List.mem_singleton, forall_eq]
          exact hp.y_c.sub_right (Offset.sub_base _ (by omega_using [])))
      (by show (16 : Nat) ≤ 2 ^ 64; decide) hk
  · -- The counter.
    dsimp only
    rw [← hcb₁]
    refine Proof.Aes.AArch64.ctr_after fun k hk => ?_
    rw [Proof.Aes.AArch64.writeW_apply, Proof.Aes.AArch64.off_toNat _ (by omega_using [hk]) (by omega_using []), hlo]
    by_cases h : 12 ≤ k
    · rw [ite_eq_left h, ite_eq_left (show k - 12 < 32 / 8 by omega_using [hk]), ite_eq_right (show ¬ k < 12 by omega_using [h]),
        BitVec.setWidth_eq]
      congr 3
      apply BitVec.eq_of_toNat_eq; simp
    · rw [ite_eq_right h, ite_eq_right (show ¬ 2 ^ 64 + k - 12 < 32 / 8 by omega_using []),
        ite_eq_left (show k < 12 by omega_using [h])]
  · -- The data.
    dsimp only
    refine dataInvM_frame (rs := [yR s₀, cR s₀]) ?_ ?_ (by omega_using [hn])
      (by have := hI.data; rw [show 8 * nb s₀ = 8 * nb s₀ from rfl] at this; exact this)
    · rw [← hm₁]
      exact (((Frame.refl _ _).write (List.mem_cons_self ..) _ (Region.contains_self _ _)).writeW
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
        (Offset.contains_base _ (by omega_using []) (by omega_using [])))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (show (⟨dp s₀, 16 * (8 * nb s₀)⟩ : Region) = dR s₀ by simp [dR]; omega_using []) ▸ hp.d_y
      · exact (show (⟨dp s₀, 16 * (8 * nb s₀)⟩ : Region) = dR s₀ by simp [dR]; omega_using []) ▸ hp.d_c
  · -- The frame.
    dsimp only
    rw [← hm₁]
    exact ((hI.frame.mono fun r hr => by simp at hr ⊢; exact .inr (.inr hr)).write (List.mem_cons_self ..) _
      (Region.contains_self _ _)).writeW (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _
      (Offset.contains_base _ (by omega_using []) (by omega_using []))
  · have hk := (kRegsT_not hr).1
    simp only [kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    dsimp only
    rw [gpr_write_of_ne _ _ _ hk.2.2.2.1, hI.gpr r hr]


/-- Interleaved encryption from x15 to x23. GHASH reads the new
ciphertext and counter mode reads the original plaintext. -/
theorem encTo_ok {s₀ : State} (hp : SealToPre s₀) (gh : Gh8Ok) :
    WP isa (.seq (.block setup) (.seq (byRounds encToLoop) (.block finish))) s₀ (SealToPost s₀) := by
  refine WP.seq (WP.mono (setup_ok hp.toKPre.toM (cipherBlock s₀)) fun _ h => ?_)
  refine WP.seq (WP.mono (byRounds_ok hp.toKPre.toM (f := encToLoop) h fun _ hi => encToLoop_ok hp gh (sealInv_start hi))
    fun _ hi => ?_)
  refine WP.mono (finishTo_ok hp hi) fun _ z => ⟨ctr32_of_dataInvM z.data, z.ctr, ?_, z.dst, z.src, z.frame,
    z.gpr, z.sp, z.rd, z.wr⟩
  rw [z.y, ctr32_of_dataInvM z.data, ctr32_eq_map]
  rfl

end VG.Proof.Gcm.AArch64.Stitch

@[expose] public section

/-! The out-of-place gather derives its interleaved GHASH table directly
from the hash subkey in the ordinary AES context. -/

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.Gcm.AArch64.Pmull
open VG.Proof.AesGcm.AArch64.Stitch (PT tblR tbl_ok)
open VG.Impl.Gcm.AArch64.Pmull (tReg sReg)
open VG.Impl.AesGcm.AArch64.DirectGather (tableFromKey)

structure DirectTablePost (s t : State) : Prop where
  tbl : TblOk t.mem (s.gpr .x19) (Spec.Gcm.ctxH s.mem (s.gpr .x21))
  frame : Frame [tblR (s.gpr .x19)] s.mem t.mem
  gpr : ∀ r, r ≠ .x0 → r ≠ .x5 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- The two algebraic facts used by the stitched machine proof. Registration
supplies them once, keeping polynomial algebra out of the descriptor loop. -/
structure GatherLaws : Prop where
  hash : Gh8Ok
  table : ∀ {s : State}, InRegions (s.rd ++ s.wr) (s.gpr .x21 + BitVec.ofNat 64 240) 16 →
    InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 512) 192 → WP isa (.block tableFromKey) s (DirectTablePost s)

end VG.Proof.Gcm.AArch64.Stitch

/-! Construct the gather sealing kernel's precondition using the ordinary
AES-GCM caller layout and the table derived in the workspace. -/

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64
open VG.Proof.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64.Stitch (tblR kpre_of tbl_ctx tbl_st pre sFrame)
open VG.Impl.AesGcm.AArch64.DirectGather (tableFromKey)
open VG.Impl.Gcm.AArch64.Stitch (setup byRounds encToLoop finish)
open VG.Spec.Gcm (Block blockAt blocksAt)

structure BatchIn (Wn : Nat) (Ctx St W SP D O : Addr) (R n : Nat) (s : State) : Prop where
  env : Env Wn Ctx St W SP s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  x23 : s.gpr .x23 = D
  x24 : s.gpr .x24 = BitVec.ofNat 64 n
  x26 : s.gpr .x26 = O
  src : DataOk Wn St W s D n
  dst : DataW Wn Ctx St W s O n
  apart : (⟨D, n⟩ : Region).Disjoint ⟨O, n⟩

/-- The kernel uses x15 for input, x23 for output, and x26 for the available length. -/
structure BatchArgs (Wn : Nat) (Ctx St W SP D O : Addr) (R n : Nat) (s : State) : Prop where
  env : Env Wn Ctx St W SP s
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  x15 : s.gpr .x15 = D
  x23 : s.gpr .x23 = O
  x26 : s.gpr .x26 = BitVec.ofNat 64 n
  src : DataOk Wn St W s D n
  dst : DataW Wn Ctx St W s O n
  apart : (⟨D, n⟩ : Region).Disjoint ⟨O, n⟩

theorem BatchArgs.sealPre {Wn R n : Nat} {Ctx St W SP D O : Addr} {s : State}
    (h : BatchArgs Wn Ctx St W SP D O R n s) (L : Lay Wn Ctx St W) (hn : 128 ≤ n)
    (tok : TblOk s.mem W (blockAt s.mem (Ctx + BitVec.ofNat 64 240))) : SealToPre s := by
  have hpre := kpre_of («to» := false) L h.env h.x22 h.rounds h.x23 h.x26 h.dst.ok h.dst
    (show O = O from rfl) hn tok h.env.perm.hWn
  have hnb : nb s = n / 128 := by simp only [nb, h.x26, toNat_ofNat_of_lt h.src.lt]
  have hpn := Nat.mul_div_le n 128
  refine ⟨hpre.toKPre, ?_, ?_, ?_⟩
  · rw [h.x15, hnb]
    exact covers_prefix h.src.rd hpn _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  · simp only [dR, dp, hnb, h.x15, h.x23]
    exact (h.apart.sub_left (Region.sub_prefix hpn)).sub_right (Region.sub_prefix hpn)
  · rw [h.x15, hnb]; have := h.src.wrap; omega

/-- The complete eight-block kernel and its table, with the original
source, key, and counter in its postcondition. -/
structure BatchMid (Ctx St W D O : Addr) (R n : Nat) (s t : State) : Prop where
  data : blocksAt t.mem O (8 * (n / 128)) = Spec.Gcm.ctr32 (ciphOf s.mem Ctx R)
    (blockAt s.mem (St + BitVec.ofNat 64 48)) (blocksAt s.mem D (8 * (n / 128)))
  ctr : blockAt t.mem (St + BitVec.ofNat 64 48) =
    Nat.repeat Spec.Gcm.inc32 (8 * (n / 128)) (blockAt s.mem (St + BitVec.ofNat 64 48))
  y : blockAt t.mem (St + BitVec.ofNat 64 16) = Spec.Gcm.ghashFrom (Spec.Gcm.ctxH s.mem Ctx)
    (blockAt s.mem (St + BitVec.ofNat 64 16)) (blocksAt t.mem O (8 * (n / 128)))
  src : t.gpr .x15 = D + BitVec.ofNat 64 (pre n)
  dst : t.gpr .x9 = O + BitVec.ofNat 64 (pre n)
  frame : Frame (sFrame St W O n) s.mem t.mem
  gpr : ∀ r, r ≠ .x0 → r ≠ .x5 → r ∉ kRegsT true → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem batchTableSeal_ok {Wn R n : Nat} {Ctx St W SP D O : Addr} {s : State}
    (h : BatchArgs Wn Ctx St W SP D O R n s) (L : Lay Wn Ctx St W) (hn : 128 ≤ n) (gh : GatherLaws) :
    WP isa (.seq (.block (tableFromKey ++ setup)) (.seq (byRounds encToLoop) (.block finish))) s
      (BatchMid Ctx St W D O R n s) := by
  rw [WP.seq_iff, WP.block_append_iff]
  have hW := h.env.perm.hWn
  refine WP.mono (gh.table (by rw [h.env.x21]; exact h.env.perm.ctxR (by decide))
    (by rw [h.env.x19]; exact h.env.perm.wWn (by omega))) fun u q => ?_
  have keep (r : Reg) (hr : r ∈ [Reg.x19, .x20, .x21]) : u.gpr r = s.gpr r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact q.gpr _ (by decide) (by decide)
  have hu : BatchArgs Wn Ctx St W SP D O R n u :=
    ⟨h.env.keep keep q.sp q.rd q.wr, h.rounds, (q.gpr _ (by decide) (by decide)).trans h.x22,
      (q.gpr _ (by decide) (by decide)).trans h.x15, (q.gpr _ (by decide) (by decide)).trans h.x23,
      (q.gpr _ (by decide) (by decide)).trans h.x26, h.src.of_eq q.rd q.wr, h.dst.of_eq q.rd q.wr, h.apart⟩
  have F : Frame [tblR W] s.mem u.mem := h.env.x19 ▸ q.frame
  have H : blockAt u.mem (Ctx + BitVec.ofNat 64 240) = Spec.Gcm.ctxH s.mem Ctx :=
    blockAt_frame F fun r hr => (tbl_ctx L r hr).sub_left (Lay.ctxSub (by decide))
  have hp := hu.sealPre L hn (by rw [H]; simpa only [h.env.x19, h.env.x21] using q.tbl)
  refine (WP.seq_iff.mp (WP.mono (encTo_ok hp gh.hash) fun t z => ?_))
  have en : nb u = n / 128 := by simp only [nb, hu.x26, toNat_ofNat_of_lt h.src.lt]
  have eR : rounds u = R := by simp only [rounds, hu.x22, toNat_rounds hu.rounds]
  have ekey : ciph u = ciphOf s.mem Ctx R := by
    unfold ciph ksch kc ciphOf
    rw [eR, hu.env.x21, bytesAt_frame F (fun r hr => (tbl_ctx L r hr).sub_left
      (Region.sub_prefix (by have := h.rounds; omega))) (by have := h.rounds; omega)]
  have ectr : icb u = blockAt s.mem (St + BitVec.ofNat 64 48) := by
    unfold icb stp; rw [hu.env.x20, blockAt_frame F (tbl_st L (by decide))]
  have ey : y₀ u = blockAt s.mem (St + BitVec.ofNat 64 16) := by
    unfold y₀ stp; rw [hu.env.x20, blockAt_frame F (tbl_st L (by decide))]
  have eh : hk u = Spec.Gcm.ctxH s.mem Ctx := by simpa only [hk, kc, hu.env.x21] using H
  have pfx : 16 * (8 * (n / 128)) ≤ n := by have := Nat.mul_div_le n 128; omega
  have esrc : blocksAt u.mem D (8 * (n / 128)) = blocksAt s.mem D (8 * (n / 128)) :=
    blocksAt_frame F (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (h.src.w.sub_left (Region.sub_prefix pfx)).sub_right (Lay.wSub (by omega)))
      (by have := h.src.lt; omega)
  refine ⟨by simpa only [en, dp, hu.x23, hu.x15, ekey, ectr, esrc] using z.data,
    by simpa only [en, stp, hu.env.x20, ectr] using z.ctr,
    by simpa only [en, stp, hu.env.x20, dp, hu.x23, eh, ey] using z.y,
    by simpa only [pre, en, hu.x15] using z.src, by simpa only [pre, en, dp, hu.x23] using z.dst,
    ?_, fun r h0 h5 hr => (z.gpr r hr).trans (q.gpr r h0 h5), z.sp.trans q.sp, z.rd.trans q.rd,
    z.wr.trans q.wr⟩
  have f := z.frame
  simp only [yR, cR, dR, dp, stp, hu.env.x20, hu.x23, en] at f
  exact (F.mono (fun r hr => by simp only [List.mem_singleton] at hr; subst r; simp)).trans
    (f.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp)

end VG.Proof.Gcm.AArch64.Stitch

/-! Gather's register shuffles and ciphertext hash cursor around the
interleaved kernel. -/

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64.Stitch (pre sFrame)
open VG.Impl.AesGcm.AArch64 (mov imm)
open VG.Impl.AesGcm.AArch64.DirectGather (tableFromKey hashO)
open VG.Impl.Gcm.AArch64.Stitch (setup byRounds encToLoop finish)
open VG.Spec.Gcm (blockAt blocksAt)

theorem batchArgs_ok {Wn R n : Nat} {Ctx St W SP D O : Addr} {s : State}
    (h : BatchIn Wn Ctx St W SP D O R n s) :
    WP isa (.block [mov .x15 .x23, mov .x23 .x26, mov .x26 .x24]) s fun u =>
      BatchArgs Wn Ctx St W SP D O R n u ∧ Regs [.x15, .x23, .x26] s u := by
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine And.symm ?_
  suffices g : Regs [.x15, .x23, .x26] s _ by
    refine ⟨g, ?_⟩
    refine ⟨h.env.keep (fun r hr => g.others r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide)) g.sp g.rd g.wr, h.rounds,
      (g.others _ (by decide)).trans h.x22, ?_, ?_, ?_, h.src.of_eq g.rd g.wr, h.dst.of_eq g.rd g.wr, h.apart⟩
    · simp [gpr_write, h.x23]
    · simp [gpr_write, h.x26]
    · simp [gpr_write, h.x24]
  exact ⟨by others_tac, rfl, rfl, rfl, rfl⟩

theorem and127 (x : BitVec 64) : x &&& BitVec.ofNat 64 127 = BitVec.ofNat 64 (x.toNat % 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 127) (by decide),
    show (127 : Nat) = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

abbrev cursorCode : List Instr := [mov .x26 .x9, mov .x23 .x15, imm .x10 127,
  .logic .and .x .x24 .x24 .x10, .str .x .x26 .x19 hashO]

structure CursorPost (s t : State) : Prop where
  src : t.gpr .x23 = s.gpr .x15
  dst : t.gpr .x26 = s.gpr .x9
  rest : t.gpr .x24 = BitVec.ofNat 64 ((s.gpr .x24).toNat % 128)
  mem : t.mem = s.mem.writeW (s.gpr .x19 + BitVec.ofNat 64 hashO) (s.gpr .x9)
  gpr : ∀ r, r ∉ [Reg.x26, .x23, .x10, .x24] → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem cursor_ok {s : State} (hw : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 hashO) 8) :
    WP isa (.block cursorCode) s (CursorPost s) := by
  change InRegions s.wr (s.gpr .x19 + 352#64) 8 at hw
  refine WP.of_runBlock ⟨_, by arun [cursorCode, hashO, hw], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · simp [gpr_write]
  · simp [gpr_write]
  · simpa [gpr_write] using and127 (s.gpr .x24)
  · simp [Mem.writeW, hashO]
  · others_tac

abbrev batchCode : Prog isa :=
  .seq (.block ([mov .x15 .x23, mov .x23 .x26, mov .x26 .x24] ++ tableFromKey ++ setup))
    (.seq (byRounds encToLoop) (.block (finish ++ cursorCode)))

structure BatchOut (Ctx St W D O : Addr) (R n : Nat) (s t : State) : Prop where
  data : blocksAt t.mem O (8 * (n / 128)) = Spec.Gcm.ctr32 (ciphOf s.mem Ctx R)
    (blockAt s.mem (St + BitVec.ofNat 64 48)) (blocksAt s.mem D (8 * (n / 128)))
  ctr : blockAt t.mem (St + BitVec.ofNat 64 48) =
    Nat.repeat Spec.Gcm.inc32 (8 * (n / 128)) (blockAt s.mem (St + BitVec.ofNat 64 48))
  y : blockAt t.mem (St + BitVec.ofNat 64 16) = Spec.Gcm.ghashFrom (Spec.Gcm.ctxH s.mem Ctx)
    (blockAt s.mem (St + BitVec.ofNat 64 16)) (blocksAt t.mem O (8 * (n / 128)))
  src : t.gpr .x23 = D + BitVec.ofNat 64 (pre n)
  dst : t.gpr .x26 = O + BitVec.ofNat 64 (pre n)
  rest : t.gpr .x24 = BitVec.ofNat 64 (n % 128)
  hashPtr : t.mem.readW (W + BitVec.ofNat 64 hashO) 64 = O + BitVec.ofNat 64 (pre n)
  frame : Frame (⟨W + BitVec.ofNat 64 hashO, 8⟩ :: sFrame St W O n) s.mem t.mem
  saved : ∀ r ∈ preserved, r ≠ .x23 → r ≠ .x24 → r ≠ .x26 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- One or more complete batches, after pending ciphertext has been hashed.
The tail of the fragment remains in the caller's cursor registers. -/
theorem batchCode_ok {Wn R n : Nat} {Ctx St W SP D O : Addr} {s : State}
    (h : BatchIn Wn Ctx St W SP D O R n s) (L : Lay Wn Ctx St W) (hn : 128 ≤ n) (gh : GatherLaws) :
    WP isa batchCode s (BatchOut Ctx St W D O R n s) := by
  rw [batchCode, List.append_assoc, WP.seq_iff, WP.block_append_iff]
  refine WP.mono (batchArgs_ok h) fun u ⟨ha, a⟩ => ?_
  have continuation := fun t (z : BatchMid Ctx St W D O R n u t) => show
      WP isa (.block cursorCode) t (BatchOut Ctx St W D O R n s) from by
    have hw : t.gpr .x19 = W := (z.gpr _ (by decide) (by decide) (by decide)).trans ha.env.x19
    have wr := z.wr.trans a.wr
    have writable := h.env.perm.wWn (d := hashO) (n := 8) (by have := L.hWn; unfold hashO; omega)
    refine WP.mono (cursor_ok (by rw [wr, hw]; exact writable)) fun v c => ?_
    have F : Frame [⟨W + BitVec.ofNat 64 hashO, 8⟩] t.mem v.mem := by
      rw [c.mem, hw]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have hyc (k : Nat) (hk : k + 16 ≤ 80) : ∀ r ∈ [⟨W + BitVec.ofNat 64 hashO, 8⟩],
        (⟨St + BitVec.ofNat 64 k, 16⟩ : Region).Disjoint r := by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact L.st_w hk (by unfold hashO; decide)
    have pfx : 16 * (8 * (n / 128)) ≤ n := by have := Nat.mul_div_le n 128; omega
    have esrc : blocksAt v.mem O (8 * (n / 128)) = blocksAt t.mem O (8 * (n / 128)) :=
      blocksAt_frame F (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.dst.ok.w.sub_left (Region.sub_prefix pfx)).sub_right (Lay.wSub (by have := L.hWn; unfold hashO; omega)))
        (by have := h.src.lt; omega)
    refine ⟨by rw [esrc, z.data, a.mem],
      by rw [blockAt_frame F (hyc 48 (by decide)), z.ctr, a.mem],
      by rw [blockAt_frame F (hyc 16 (by decide)), z.y, a.mem, esrc],
      c.src.trans z.src, c.dst.trans z.dst, ?_, ?_, ?_, ?_, c.sp.trans (z.sp.trans a.sp),
      c.rd.trans (z.rd.trans a.rd), c.wr.trans wr⟩
    · rw [c.rest, z.gpr _ (by decide) (by decide) (by decide), a.others _ (by decide), h.x24,
        toNat_ofNat_of_lt h.src.lt]
    · rw [c.mem, hw, Mem.readW_writeW_self64, z.dst]
    · rw [← a.mem]
      exact (z.frame.mono (fun r hr => List.mem_cons_of_mem _ hr)).trans
        (F.mono (fun r hr => by simp only [List.mem_singleton] at hr; exact List.mem_cons.mpr (.inl hr)))
    · intro r hr h23 h24 h26
      have h5 : r ≠ .x5 := fun e => by subst r; contradiction
      have h0 : r ≠ .x0 := fun e => by subst r; contradiction
      have hsmall (j : Reg) (hj : j ∉ preserved) : r ≠ j := fun e => hj (e ▸ hr)
      rw [c.gpr, z.gpr r h0 h5, a.others]
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hsmall _ (by decide), h23, h26⟩
      · simp only [kRegsT, Bool.cond_true, kRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hsmall _ (by decide), hsmall _ (by decide), hsmall _ (by decide), hsmall _ (by decide),
          hsmall _ (by decide), hsmall _ (by decide), hsmall _ (by decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h26, h23, hsmall _ (by decide), h24⟩
  refine WP.mono (WP.seq_iff.mp (WP.mono (batchTableSeal_ok ha L hn gh) continuation)) fun _ next => ?_
  refine WP.seq (WP.mono (WP.seq_iff.mp next) fun _ doneBatches => ?_)
  exact WP.block_append_iff.mpr doneBatches

end VG.Proof.Gcm.AArch64.Stitch

/-! Hash complete ciphertext blocks left between the previous interleaved
batch and the current block-aligned destination. -/

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64 (ghArgs)
open VG.Impl.AesGcm.AArch64.DirectGather (hashPending hashO)
open VG.Spec.Gcm (blockAt blocksAt)

theorem pendingCursor {Wn n : Nat} {Ctx St W SP P : Addr} {s : State}
    (he : Env Wn Ctx St W SP s) (slot : s.mem.readW (W + BitVec.ofNat 64 hashO) 64 = P)
    (stop : s.gpr .x26 = P + BitVec.ofNat 64 (16*n)) (data : DataOk Wn St W s P (16*n)) :
    ∃ u, runBlock isa [.ldr .x .x2 .x19 hashO, .sub .x .x3 .x26 .x2, .lsr .x .x3 .x3 4] s = some u ∧
      u.gpr .x2 = P ∧ u.gpr .x3 = BitVec.ofNat 64 n ∧ Regs [.x2, .x3] s u := by
  have rd := he.perm.wRn (d := hashO) (n := 8) (by have := he.perm.hWn; unfold hashO; omega)
  change InRegions (s.rd ++ s.wr) (W + 352#64) 8 at rd
  have load : s.mem.read (W + 352#64) 8 = P := slot
  refine ⟨_, by arun [he.x19, rd, hashO], ?_⟩
  refine ⟨?_, ?_, by others_tac, rfl, rfl, rfl, rfl⟩
  · simpa [gpr_write] using load
  · simp only [gpr_write, Size.bits, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
      load, stop, BitVec.add_comm P, BitVec.add_sub_cancel]
    rw [lsr_ofNat _ _ data.lt, show 16 * n / 2 ^ 4 = n by omega]

theorem pendingGhArgs {Wn : Nat} {Ctx St W SP : Addr} {u : State} (env : Env Wn Ctx St W SP u) :
    ∃ t, runBlock isa (ghArgs 16) u = some t ∧
      t.gpr .x0 = Ctx + BitVec.ofNat 64 240 ∧ t.gpr .x1 = St + BitVec.ofNat 64 16 ∧
      t.gpr .x4 = W + BitVec.ofNat 64 512 ∧ Regs [.x0, .x1, .x4] u t := by
    refine ⟨_, by arun [ghArgs], ?_⟩
    refine ⟨?_, ?_, ?_, by others_tac, rfl, rfl, rfl, rfl⟩ <;>
      simp [gpr_write, env.x19, env.x20, env.x21]

theorem pendingGhCall {Wn n : Nat} {Ctx St W SP P : Addr} {u t : State}
    (L : Lay Wn Ctx St W) (env : Env Wn Ctx St W SP u) (data : DataOk Wn St W u P (16*n))
    (e2 : u.gpr .x2 = P) (e3 : u.gpr .x3 = BitVec.ofNat 64 n) (e0 : t.gpr .x0 = Ctx+240#64)
    (e1 : t.gpr .x1 = St+16#64) (e4 : t.gpr .x4 = W+512#64) (rt : Regs [.x0,.x1,.x4] u t) :
    GhCall t (Ctx+240#64) (St+16#64) P (W+512#64) n := by
  have et := env.keep (fun j hj => rt.others j (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl <;> decide)) rt.sp rt.rd rt.wr
  exact ghCall_of L (.inr rfl) et e0 e1 ((rt.others _ (by decide)).trans e2)
      ((rt.others _ (by decide)).trans e3) e4 data.lt (data.st.symm.sub_left (Lay.stSub (by decide)))
      (data.w.sub_right (Lay.wSub (by have := L.hWn; omega))) (by rw [rt.rd, rt.wr]; exact data.rd)

theorem hashPending_ok (v : GcmImpl) {Wn n : Nat} {Ctx St W SP P : Addr} {s : State}
    (L : Lay Wn Ctx St W) (he : Env Wn Ctx St W SP s)
    (slot : s.mem.readW (W + BitVec.ofNat 64 hashO) 64 = P)
    (stop : s.gpr .x26 = P + BitVec.ofNat 64 (16 * n)) (data : DataOk Wn St W s P (16 * n)) :
    WP isa (hashPending v.callees) s (GhPost s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 16)
      P (W + BitVec.ofNat 64 512) n) := by
  obtain ⟨u, run, e2, e3, r⟩ := pendingCursor he slot stop data
  have env := he.keep (fun j hj => r.others j (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl <;> decide)) r.sp r.rd r.wr
  refine WP.seq (WP.of_runBlock ⟨u, run, ?_⟩)
  refine WP.ite _ (Proof.Aes.AArch64.Aese.eval_zero e3 (by have := data.lt; omega)) (fun hz => ?_) (fun _ => ?_)
  · obtain rfl : n = 0 := by simpa using hz
    refine WP.block_nil ⟨r.rd, r.wr, r.sp, fun j hj _ => r.others j ?_, r.mem ▸ Frame.refl _ _, ?_⟩
    · intro hj'; simp only [List.mem_cons, List.not_mem_nil, or_false] at hj'
      rcases hj' with rfl | rfl <;> contradiction
    · rw [r.mem]; rfl
  · obtain ⟨t, run', e0, e1, e4, rt⟩ := pendingGhArgs env
    refine WP.seq (WP.of_runBlock ⟨t, run', ?_⟩)
    have hcall := pendingGhCall L env (data.of_eq r.rd r.wr) e2 e3 e0 e1 e4 rt
    refine WP.mono (gh_call v.gh hcall) fun z q => ⟨q.rd.trans (rt.rd.trans r.rd), q.wr.trans (rt.wr.trans r.wr),
      q.sp.trans (rt.sp.trans r.sp), fun j hj h30 => ?_, ?_, ?_⟩
    · rw [q.saved j hj h30, rt.others, r.others] <;>
        intro hj' <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hj' <;>
        repeat' first | contradiction | rcases hj' with rfl | hj'
    · simpa only [rt.mem, r.mem] using q.frame
    · simpa only [rt.mem, r.mem] using q.out

end VG.Proof.Gcm.AArch64.Stitch

/-! The actual length guard, pending GHASH, and interleaved batches of one
gather descriptor. -/

namespace VG.Proof.Gcm.AArch64.Stitch
open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.AesGcm.AArch64
open VG.Impl.AesGcm.AArch64.DirectGather (batches hashO)
open VG.Spec.Gcm (blockAt blocksAt)

abbrev batchTest (n : Nat) : BitVec 64 :=
  (BitVec.ofNat 64 n + BitVec.ofNat 64 (1024 - Impl.AesGcm.AArch64.Stitch.minLen)) >>> 10

theorem batchTest_len {n : Nat} (h : batchTest n ≠ 0) : 128 ≤ n := by
  by_cases hn : 128 ≤ n
  · exact hn
  exfalso
  apply h
  unfold batchTest Impl.AesGcm.AArch64.Stitch.minLen
  rw [ofNat_add_ofNat, lsr_ofNat _ _ (by omega)]
  have : (n + (1024 - 768)) / 2 ^ 10 = 0 := by omega
  rw [this]; rfl

structure PendingIn (Wn : Nat) (St W P O : Addr) (k : Nat) (s : State) : Prop where
  slot : s.mem.readW (W + BitVec.ofNat 64 hashO) 64 = P
  stop : O = P + BitVec.ofNat 64 (16 * k)
  data : DataOk Wn St W s P (16 * k)

/-- Either the size guard skipped this fragment, or its pending ciphertext was
hashed from the original accumulator before the complete batches ran. -/
def BatchesPost (Ctx St W D O P : Addr) (R n k : Nat) (s t : State) : Prop :=
  (batchTest n = 0 ∧ Regs [.x9] s t) ∨
  (batchTest n ≠ 0 ∧ ∃ u, GhPost s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 16) P
    (W + BitVec.ofNat 64 512) k u ∧ BatchOut Ctx St W D O R n u t)

theorem batchGuard {Wn R n : Nat} {Ctx St W SP D O : Addr} {s : State}
    (h : BatchIn Wn Ctx St W SP D O R n s) :
    ∃ a, runBlock isa [.addImm .x .x9 .x24 (1024 - Impl.AesGcm.AArch64.Stitch.minLen),
      .lsr .x .x9 .x9 10] s = some a ∧ a.gpr .x9 = batchTest n ∧ Regs [.x9] s a := by
  refine ⟨_, by arun [Impl.AesGcm.AArch64.Stitch.minLen], ?_⟩
  exact ⟨by simp [batchTest, gpr_write, h.x24, Impl.AesGcm.AArch64.Stitch.minLen],
    by others_tac, rfl, rfl, rfl, rfl⟩

theorem batches_ok (v : GcmImpl) {Wn R n k : Nat} {Ctx St W SP D O P : Addr} {s : State}
    (h : BatchIn Wn Ctx St W SP D O R n s) (L : Lay Wn Ctx St W) (gh : GatherLaws)
    (pending : batchTest n ≠ 0 → PendingIn Wn St W P O k s) :
    WP isa (batches v.callees) s (BatchesPost Ctx St W D O P R n k s) := by
  obtain ⟨a, run, test, r⟩ := batchGuard h
  have keep (j : Reg) (hj : j ∈ preserved) : a.gpr j = s.gpr j := r.others j (by
    simp only [List.mem_singleton]; intro e; subst j; contradiction)
  have ea := h.env.of_saved (fun j hj _ => keep j hj) r.sp r.rd r.wr
  refine WP.seq (WP.of_runBlock ⟨a, run, ?_⟩)
  have eval : AArch64.eval (.zero .x .x9) a = some (decide (batchTest n = 0)) := by
    change some (a.gpr .x9 == (0 : BitVec 64)) = _
    rw [test]
    by_cases hz : batchTest n = 0
    · rw [hz]; rfl
    · rw [beq_eq_false_iff_ne.mpr hz, decide_eq_false hz]
  refine WP.ite _ eval (fun z => ?_) (fun nz => ?_)
  · exact WP.block_nil (.inl ⟨by simpa using z, r⟩)
  · have hn : batchTest n ≠ 0 := by simpa using nz
    have hp := pending hn
    refine WP.seq (WP.mono (hashPending_ok v L ea (r.mem ▸ hp.slot)
      ((keep _ (by decide)).trans (h.x26.trans hp.stop)) (hp.data.of_eq r.rd r.wr)) fun u p => ?_)
    have saved (j : Reg) (hj : j ∈ preserved) (h30 : j ≠ .x30) :
        u.gpr j = s.gpr j := (p.saved j hj h30).trans (keep j hj)
    have rd := p.rd.trans r.rd
    have wr := p.wr.trans r.wr
    have g : GhPost s (Ctx + BitVec.ofNat 64 240) (St + BitVec.ofNat 64 16) P
        (W + BitVec.ofNat 64 512) k u :=
      ⟨rd, wr, p.sp.trans r.sp, saved, r.mem ▸ p.frame, by simpa only [r.mem] using p.out⟩
    have hu : BatchIn Wn Ctx St W SP D O R n u :=
      ⟨h.env.of_saved saved g.sp rd wr, h.rounds, (saved _ (by decide) (by decide)).trans h.x22,
        (saved _ (by decide) (by decide)).trans h.x23, (saved _ (by decide) (by decide)).trans h.x24,
        (saved _ (by decide) (by decide)).trans h.x26, h.src.of_eq rd wr, h.dst.of_eq rd wr, h.apart⟩
    exact WP.mono (batchCode_ok hu L (batchTest_len hn) gh) fun t out => .inr ⟨hn, u, g, out⟩

end VG.Proof.Gcm.AArch64.Stitch
