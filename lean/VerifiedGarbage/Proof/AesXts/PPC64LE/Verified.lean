module

public import VerifiedGarbage.Impl.AesXts.PPC64LE
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Spec.Xts.Contract
import VerifiedGarbage.Proof.AesXts.PPC64LE.Body
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Group
import VerifiedGarbage.Proof.AesXts.PPC64LE.Steps
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.AesXts.PPC64LE
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Call
meta import VerifiedGarbage.Proof.AesXts.Spec
meta import VerifiedGarbage.Spec.Xts.Contract
meta import VerifiedGarbage.Proof.AesXts.PPC64LE.Body
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Group
meta import VerifiedGarbage.Proof.AesXts.PPC64LE.Steps
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# XTS-AES on PPC64LE: the contracts

`Verified` for `vg_aes_xts_encrypt` and `vg_aes_xts_decrypt`: AES-CBC's
`whole_wp` and `whole_ct` (`Proof/AesCbc/PPC64LE/`) with the bodies of
`Body.lean`, and the contracts of `Spec/Xts/Contract.lean` from
`modePPC64LE (xtsMode enc)`.
-/

@[expose] public section

namespace VG.Proof.AesXts.PPC64LE

open VG VG.PPC64LE VG.Impl.AesXts.PPC64LE
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.PPC64LE
open VG.Proof.AesCbc (xorMem xorMem_frame xorMem_bytes copyMem copyMem_frame copyMem_bytes aesWith_state
  aesInvWith_state)
open VG.Impl.AesCbc.PPC64LE (xorAt copy slot fixSlots callArgs8 advance8 encCall decCall)
open VG.Spec.Aes (bytesAt)

/-! ## Eight blocks at a time -/

/-- XTS extends its output one block at a time. -/
theorem xts_steps (enc : Bool) :
    Steps (AesXts.xtsMode enc) fun R w x c => Spec.Xts.block (ciphOf enc R w) c x := by
  intro R w t xs x
  simp only [AesXts.xtsMode_out, AesXts.xtsMode_chain, AesXts.crypt_snoc]

/-- The tweak after block `i` is the one before it times `α`. -/
theorem xts_chain (enc : Bool) (s₀ : State) {i : Nat} (hi : i < N s₀) :
    chainK (AesXts.xtsMode enc) s₀ (i + 1) = Spec.Xts.mulAlpha (chainK (AesXts.xtsMode enc) s₀ i) := by
  have hlt : ((blks s₀).take i).length = i := by simp [Spec.Cbc.blocksAt]; omega
  simp only [chainK, AesXts.xtsMode_chain, take_succ_blkOf s₀ hi, List.length_append, List.length_singleton,
    hlt, AesXts.next_succ]

/-- After the tweaks of the first `m` blocks of a group. -/
structure TInv (enc : Bool) (s₀ : State) (k m : Nat) (s t : State) : Prop where
  g : ∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → r ≠ .r12 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨blk s₀ k, 16 * m⟩, ivR s₀, ⟨S s₀, 144⟩] s.mem t.mem
  blk : ∀ j < m, bytesAt t.mem (blk s₀ (k + j)) 16 =
    Spec.Cbc.xor (blkOf s₀ (k + j)) (chainK (AesXts.xtsMode enc) s₀ (k + j))
  slot : ∀ j < m, bytesAt t.mem (sl s₀ j) 16 = chainK (AesXts.xtsMode enc) s₀ (k + j)
  iv : bytesAt t.mem (Iv s₀) 16 = chainK (AesXts.xtsMode enc) s₀ (k + m)

theorem tweaks_wp (enc : Bool) {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 8 ≤ N s₀) {s : State}
    (h : LInv (AesXts.xtsMode enc) s₀ k s) (m : Nat) (hm : m ≤ 8) {rest : List Instr} {Φ : State → Prop}
    (cont : ∀ t, TInv enc s₀ k m s t → WP isa (.block rest) t Φ) :
    WP isa (.block ((List.range m).flatMap tweakAt ++ rest)) s Φ := by
  induction m generalizing rest Φ with
  | zero =>
    exact cont s ⟨fun _ _ _ _ _ => rfl, rfl, rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun j hj => absurd hj (Nat.not_lt_zero _), h.iv⟩
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.append_assoc]
    refine ih (by omega) fun t ht => ?_
    have hR : t.rd ++ t.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [ht.rd, ht.wr, h.regs hp]
    have hW : t.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [ht.wr, h.wrs hp]
    have r16 : t.gpr .r16 = Iv s₀ := by rw [ht.g _ (by decide) (by decide) (by decide) (by decide), h.r16]
    have r17 : t.gpr .r17 = blk s₀ k := by rw [ht.g _ (by decide) (by decide) (by decide) (by decide), h.r17]
    have r19 : t.gpr .r19 = S s₀ := by rw [ht.g _ (by decide) (by decide) (by decide) (by decide), h.r19]
    simp only [tweakAt, List.append_assoc]
    refine xorAt_wp (P := blk s₀ (k + m)) (Q := Iv s₀) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) ⟨by omega, by omega⟩ ⟨by decide, by decide⟩
      (by rw [r17, blk_add]) (by rw [r17, blk_add8]) (by rw [r16, ofNat_zero_add]) (by rw [r16])
      (by rw [hR]; exact in_rw (by simp) (hp.cBlk0 (k := k + m) (by omega)))
      (by rw [hR]; exact in_rw (by simp) (hp.cBlk8 (k := k + m) (by omega)))
      (by rw [hR]; exact in_rw (by simp) cIv0) (by rw [hR]; exact in_rw (by simp) cIv8)
      (by rw [hW]; exact in_rw (by simp) (hp.cBlk0 (k := k + m) (by omega)))
      (by rw [hW]; exact in_rw (by simp) (hp.cBlk8 (k := k + m) (by omega)))
      fun t₁ g₁ mem₁ rd₁ wr₁ => ?_
    refine copy_wp (P := sl s₀ m) (Q := Iv s₀) (by decide) (by decide) (by decide) (by decide)
      ⟨by simp only [slot]; omega, by simp only [slot]; omega⟩ (by decide)
      (by rw [g₁ _ (by decide) (by decide), r19]) (by rw [g₁ _ (by decide) (by decide), r19, sl8])
      (by rw [g₁ _ (by decide) (by decide), r16, ofNat_zero_add]) (by rw [g₁ _ (by decide) (by decide), r16])
      (by rw [rd₁, wr₁, hR]; exact in_rw (by simp) cIv0) (by rw [rd₁, wr₁, hR]; exact in_rw (by simp) cIv8)
      (by rw [wr₁, hW]; exact in_rw (by simp) (cSl s₀ (by omega)))
      (by rw [wr₁, hW]; exact in_rw (by simp) (cSl8 s₀ (by omega))) fun t₂ g₂ mem₂ rd₂ wr₂ => ?_
    refine mulA_wp (Q := Iv s₀) (by rw [g₂ _ (by decide), g₁ _ (by decide) (by decide), r16])
      (by rw [rd₂, wr₂, rd₁, wr₁, hR]; exact in_rw (by simp) cIv0)
      (by rw [rd₂, wr₂, rd₁, wr₁, hR]; exact in_rw (by simp) cIv8)
      (by rw [wr₂, wr₁, hW]; exact in_rw (by simp) cIv0) (by rw [wr₂, wr₁, hW]; exact in_rw (by simp) cIv8)
      fun t₃ g₃ mem₃ rd₃ wr₃ => cont t₃ ?_
    have bIv : (⟨blk s₀ (k + m), 16⟩ : Region).Disjoint (ivR s₀) := hp.blk_iv (by omega)
    have sIv : (⟨sl s₀ m, 16⟩ : Region).Disjoint (ivR s₀) := (hp.dIS (by omega)).symm
    have bS : (⟨blk s₀ (k + m), 16⟩ : Region).Disjoint ⟨sl s₀ m, 16⟩ := hp.dBS (by omega) (by omega)
    have tIn : bytesAt t.mem (blk s₀ (k + m)) 16 = blkOf s₀ (k + m) := by
      rw [bytesAt_frame ht.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.dB_run (by omega) (.inr (Nat.le_refl _)) (by omega)
        · exact bIv
        · exact hp.dBG (by omega)) (by decide), h.blockAt (by omega) (by omega)]
    refine ⟨fun r h9 h10 h11 h12 => by rw [g₃ r h9 h10 h11 h12, g₂ r h9, g₁ r h9 h10, ht.g r h9 h10 h11 h12],
      by rw [rd₃, rd₂, rd₁, ht.rd], by rw [wr₃, wr₂, wr₁, ht.wr], ?_, fun j hj => ?_, fun j hj => ?_, ?_⟩
    · rw [mem₃, mem₂, mem₁]
      refine (ht.frame.sub fun r hr => ?_).trans (((xorMem_frame _ _ _).sub fun r hr => ?_).trans
        (((copyMem_frame _ _ _).sub fun r hr => ?_).trans ((AesXts.PPC64LE.alphaMem_frame _ _).sub fun r hr => ?_)))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨⟨blk s₀ k, 16 * (m + 1)⟩, by simp, Region.sub_prefix (by omega)⟩
        · exact ⟨ivR s₀, by simp, fun _ h => h⟩
        · exact ⟨⟨S s₀, 144⟩, by simp, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, blk_sub_run s₀⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨⟨S s₀, 144⟩, by simp, sl_sub s₀ (by omega)⟩
      · simp only [List.mem_singleton] at hr; subst hr; exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · rw [mem₃, bytesAt_frame (AesXts.PPC64LE.alphaMem_frame _ _) (one_disj ?_) (by decide), mem₂]
      · by_cases hjm : j < m
        · rw [copyMem_other _ (hp.dBS (by omega) (by omega)), mem₁,
            xorMem_other _ (hp.dBB (by omega) (by omega) (by omega)), ht.blk j hjm]
        · have : j = m := by omega
          subst this
          rw [copyMem_other _ bS, mem₁, xorMem_bytes _ bIv, tIn, ht.iv]
      · exact hp.blk_iv (by omega)
    · rw [mem₃, bytesAt_frame (AesXts.PPC64LE.alphaMem_frame _ _) (one_disj (hp.dIS (by omega)).symm)
        (by decide), mem₂]
      by_cases hjm : j < m
      · rw [copyMem_other _ (dSS s₀ (by omega) (by omega) (by omega)), mem₁,
          xorMem_other _ (hp.dBS (by omega) (by omega)).symm, ht.slot j hjm]
      · have : j = m := by omega
        subst this
        rw [copyMem_bytes _ sIv, mem₁, xorMem_other _ bIv.symm, ht.iv]
    · rw [mem₃, AesXts.PPC64LE.alphaMem_bytes, mem₂, copyMem_other _ sIv.symm, mem₁, xorMem_other _ bIv.symm,
        ht.iv, ← Nat.add_assoc, xts_chain enc s₀ (by omega)]

/-- The code before the call of a group: the call's arguments, the blocks
with their tweaks XORed in, and the tweaks in the slots. -/
theorem pre8_wp (enc : Bool) {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k + 8 ≤ N s₀) {s : State}
    (h : LInv (AesXts.xtsMode enc) s₀ k s) :
    WP isa (.block pre8) s fun s₂ =>
      CallPre8 s₂ (W s₀) (blk s₀ k) (S s₀) (R s₀) ∧ (∀ r ∈ preserved, s₂.gpr r = s.gpr r) ∧
      s₂.rd = s.rd ∧ s₂.wr = s.wr ∧ Frame [⟨blk s₀ k, 16 * 8⟩, ivR s₀, ⟨S s₀, 144⟩] s.mem s₂.mem ∧
      (∀ j < 8, bytesAt s₂.mem (blk s₀ (k + j)) 16 =
        Spec.Cbc.xor (blkOf s₀ (k + j)) (chainK (AesXts.xtsMode enc) s₀ (k + j))) ∧
      (∀ j < 8, bytesAt s₂.mem (sl s₀ j) 16 = chainK (AesXts.xtsMode enc) s₀ (k + j)) ∧
      bytesAt s₂.mem (Iv s₀) 16 = chainK (AesXts.xtsMode enc) s₀ (k + 8) := by
  rw [pre8]
  refine tweaks_wp enc hp hk h 8 (by decide) fun t ht =>
    callArgs8_wp fun s₂ r3₂ r4₂ r5₂ r6₂ r7₂ o₂ mem₂ rd₂ wr₂ => ?_
  have g' (r : Reg) (h9 : r ≠ .r9) (h10 : r ≠ .r10) (h11 : r ≠ .r11) (h12 : r ≠ .r12) : t.gpr r = s.gpr r :=
    ht.g r h9 h10 h11 h12
  refine ⟨hp.callPre8 hk (by rw [r3₂, g' _ (by decide) (by decide) (by decide) (by decide), h.r14])
    (by rw [r4₂, g' _ (by decide) (by decide) (by decide) (by decide), h.r15])
    (by rw [r5₂, g' _ (by decide) (by decide) (by decide) (by decide), h.r17]) r6₂
    (by rw [r7₂, g' _ (by decide) (by decide) (by decide) (by decide), h.r19])
    (by rw [rd₂, ht.rd, h.rd]) (by rw [wr₂, ht.wr, h.wr]), fun r hr => ?_, by rw [rd₂, ht.rd],
    by rw [wr₂, ht.wr], by rw [mem₂]; exact ht.frame, fun j hj => by rw [mem₂]; exact ht.blk j hj,
    fun j hj => by rw [mem₂]; exact ht.slot j hj, by rw [mem₂]; exact ht.iv⟩
  obtain ⟨h3, h4, h5, h6, h7, h9, h10⟩ := preserved_ne hr
  obtain ⟨-, -, h11, h12⟩ := preserved_ne' hr
  rw [o₂ r (by simp [argRegs5, h3, h4, h5, h6, h7]), ht.g r h9 h10 h11 h12]

/-- Eight blocks in the direction `enc`, by the block function `f`, which
computes `ciphOf enc` on bytes. -/
theorem group_ok (enc : Bool) {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String}
    {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.PPC64LE.blocksFramed f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.PPC64LE.blocksFramed f).post s s')
    (nf : c.noFrames = true)
    (hf : ∀ R w m p, (f R w (Spec.Aes.stateAt m p)).toList = ciphOf enc R w (bytesAt m p 16)) :
    GroupOk (AesXts.xtsMode enc) (group (.call name c)) := by
  intro s₀ hp k hk s h
  refine WP.seq (WP.mono (pre8_wp enc hp hk h) fun s₂ ⟨pre, g₂, rd₂, wr₂, f₂, b₂, sl₂, iv₂⟩ => ?_)
  refine WP.seq (WP.mono (blk_call8 ok nf pre) fun s₃ c => ?_)
  have g₃ (r : Reg) (hr : r ∈ preserved) : s₃.gpr r = s.gpr r := by rw [c.saved r hr, g₂ r hr]
  have hR₃ : s₃.rd ++ s₃.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [c.rd, c.wr, rd₂, wr₂, h.regs hp]
  have hW₃ : s₃.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, wr₂, h.wrs hp]
  have big₂ : Frame (Big s₀) s₀.mem s₂.mem :=
    (UPre.big_of h.frame).trans (f₂.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨dataR s₀, by simp, Offset.sub_base _ (by have := hp.data_wrap; omega)⟩
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩)
  rw [fixSlots]
  refine fixes_wp hp 8 (by decide) hk (by rw [g₃ _ (by decide), h.r17]) (by rw [g₃ _ (by decide), h.r19])
    hR₃ hW₃ fun s₄ g₄ rd₄ wr₄ f₄ e₄ => ?_
  have g₄' (r : Reg) (hr : r ∈ preserved) : s₄.gpr r = s.gpr r := by
    obtain ⟨-, -, -, -, -, h9, h10⟩ := preserved_ne hr
    rw [g₄ r h9 h10, g₃ r hr]
  refine advance8_regs (s := s₄) hk (by rw [g₄' _ (by decide), h.r17]) (by rw [g₄' _ (by decide), h.r18])
    fun s₆ r17₆ r18₆ keep₆ mem₆ rd₆ wr₆ => ?_
  have g (r : Reg) (hr : r ∈ preserved) (h17 : r ≠ .r17) (h18 : r ≠ .r18) : s₆.gpr r = s.gpr r := by
    rw [keep₆ r h17 h18, g₄' r hr]
  refine group_step (xts_steps enc) hp hk h ?_ ?_ ?_ r17₆ r18₆ ?_ (fun r hr hv => ?_) ?_ ?_ ?_
    (fun j hj => ?_) ?_
  · rw [g .r14 (by decide) (by decide) (by decide), h.r14]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [g .r16 (by decide) (by decide) (by decide), h.r16]
  · rw [g .r19 (by decide) (by decide) (by decide), h.r19]
  · exact g r hr (fun e => hv (by simp [e])) (fun e => hv (by simp [e]))
  · rw [rd₆, rd₄, c.rd, rd₂]
  · rw [wr₆, wr₄, c.wr, wr₂]
  · rw [mem₆]
    refine (f₂.sub fun r hr => ?_).trans ((c.frame.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨_, by simp, fun _ h => h⟩
      · exact ⟨ivR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨S s₀, 2064⟩, by simp, slR_sub s₀⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩
  · have hc := c.out j hj
    rw [blk_add] at hc
    rw [mem₆, e₄ j hj, hc, hf, UPre.sched_bytes hp big₂, b₂ j hj,
      bytesAt_frame c.frame (one_disj (hp.dSB (by omega) hk)) (by decide), sl₂ j hj]
    rfl
  · rw [mem₆, bytesAt_frame f₄ (one_disj (hp.dIB hk)) (by decide),
      bytesAt_frame c.frame (one_disj (hp.dIB hk)) (by decide), iv₂]

theorem pre8_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block pre8) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem post8_taint : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19])
    (.block (fixSlots ++ advance8)) h).isSome = true := ⟨_, by taint_decide⟩

theorem group_ct {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} (enc : Bool) {name : String}
    {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (okF : ∀ s, (Proof.Aes.PPC64LE.blocksFramed f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.PPC64LE.blocksFramed f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksPPC64LE f).pre (Proof.Aes.blocksPPC64LE f).pub c)
    (nf : c.noFrames = true) : GroupCt (AesXts.xtsMode enc) (group (.call name c)) :=
  fun hp hp' hq k => AesCbc.PPC64LE.group_ct (D := fun s₀ k => blk s₀ k) (Sc := S) (fun hq k => pub_blk hq k)
    (fun hq => pub_S hq) ok okF ct nf pre8_taint post8_taint
    (@fun _ hp _ hk _ h => WP.mono (pre8_wp enc hp hk h) fun _ a => ⟨a.1, a.2.1⟩) hp hp' hq k

theorem encGroup_ok : GroupOk (AesXts.xtsMode true) (group encCall) :=
  group_ok true Proof.Aes.PPC64LE.encryptBlocks_framed encryptBlocks_noFrames
    fun _ _ _ _ => (aesWith_state _ _ _ _).symm

theorem decGroup_ok : GroupOk (AesXts.xtsMode false) (group decCall) :=
  group_ok false Proof.Aes.PPC64LE.decryptBlocks_framed decryptBlocks_noFrames
    fun _ _ _ _ => (aesInvWith_state _ _ _ _).symm

theorem encGroup_ct : GroupCt (AesXts.xtsMode true) (group encCall) :=
  group_ct true Proof.Aes.PPC64LE.encryptBlocks_correct Proof.Aes.PPC64LE.encryptBlocks_framed
    Proof.Aes.PPC64LE.encryptBlocks_ct encryptBlocks_noFrames

theorem decGroup_ct : GroupCt (AesXts.xtsMode false) (group decCall) :=
  group_ct false Proof.Aes.PPC64LE.decryptBlocks_correct Proof.Aes.PPC64LE.decryptBlocks_framed
    Proof.Aes.PPC64LE.decryptBlocks_ct decryptBlocks_noFrames

theorem encrypt_correct (s : State) (hs : (modePPC64LE (AesXts.xtsMode true)).pre s) :
    ∃ t s', Exec isa encrypt s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (AesXts.xtsMode true)).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := batched_wp encGroup_ok encBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem decrypt_correct (s : State) (hs : (modePPC64LE (AesXts.xtsMode false)).pre s) :
    ∃ t s', Exec isa decrypt s t s' ∧ abiPreserved s s' ∧ (modePPC64LE (AesXts.xtsMode false)).post s s' := by
  obtain ⟨t, s', he, hg, hlr, hp⟩ := batched_wp decGroup_ok decBody_ok hs
  exact ⟨t, s', he, ⟨hg, Exec.sp he, hlr⟩, hp⟩

theorem encrypt_ct : ConstantTime isa (modePPC64LE (AesXts.xtsMode true)).pre
    (modePPC64LE (AesXts.xtsMode true)).pub encrypt :=
  batched_ct encGroup_ok encGroup_ct encBody_ok encBody_ct

theorem decrypt_ct : ConstantTime isa (modePPC64LE (AesXts.xtsMode false)).pre
    (modePPC64LE (AesXts.xtsMode false)).pub decrypt :=
  batched_ct decGroup_ok decGroup_ct decBody_ok decBody_ct

theorem encrypt_noFrames : encrypt.noFrames = true := by decide +kernel

theorem decrypt_noFrames : decrypt.noFrames = true := by decide +kernel

end VG.Proof.AesXts.PPC64LE
