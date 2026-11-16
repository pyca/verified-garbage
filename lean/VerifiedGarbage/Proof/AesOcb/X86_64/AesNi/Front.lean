module

public import VerifiedGarbage.Proof.AesOcb.X86_64.AesNi.Pass
public import VerifiedGarbage.Proof.AesOcb.X86_64.NonceBlock
public import VerifiedGarbage.Proof.AesOcb.X86_64.PadTo
public import VerifiedGarbage.Proof.AesOcb.X86_64.Offset0
public import VerifiedGarbage.Proof.AesOcb.X86_64.XorPad
import VerifiedGarbage.Proof.Ocb.Nonce
public import VerifiedGarbage.Proof.AesOcb.X86_64.Env
public import VerifiedGarbage.Proof.Framework.X86_64.KeepReg
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesOcb.X86_64.Run
import VerifiedGarbage.Proof.AesCcm.X86_64.Env
import VerifiedGarbage.Proof.Ocb.State
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesOcb.X86_64.Args
import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
import VerifiedGarbage.Proof.Framework.WriteBytes
-- separate module: the one-pass proofs are a chain of modules (`Pass`, `Front`, `Top`), so that a change rebuilds only the modules after it

/-!
# One-pass AES-OCB with AES-NI on x86-64: the pieces around the passes

Untrusted: everything here is checked by Lean. `one_ok`: AES of `xmm0`, as
OCB's `ENCIPHER` of its block. `ktop_ok`: `Ktop`, the nonce block
enciphered in place at `W + tmpO`.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64.AesNi

open VG VG.X86_64 VG.X86_64.RegUpd
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block blockAtMem aesWith ctxCiph lAt)
open VG.Proof.AesOcb.X86_64 (rv blockAtMem_eq blockAtMem_writeW rv_xor LayN PermN EnvN BufN DBufN NoncePost
  nonceBlock_ok padTo_ok xorPad_ok)
open VG.Proof.Aes.X86_64.AesNi (Keys st aes_ok XFrame)
open VG.Proof.AesCcm.X86_64 (in_off in_left covers_left shr4 and15')
open VG.Impl.AesOcb.X86_64 (at_ ld st tmpO rndO aadO alenO sumO t2O padTo)
open VG.Impl.AesOcb.X86_64AesNi (one ktop keys keysR lastKey hash Mode l2O l3O ljO cO ofO nonce ldx rest)
open VG.Impl.AesOcb.X86_64 (xorPad)
open VG.Impl.AesOcb.X86_64AesNi (addPad restHead tag)
open VG.Impl.AesOcb.X86_64 (ldO dataO lenO)
open VG.Impl.AesOcb.X86_64AesNi (body imcO)

/-! ## Code that keeps the SSE registers -/

/-- Code without calls or frames whose instructions write no vector
register. -/
def xmmFree : Prog isa → Bool
  | .block is => is.all fun i => !KeepReg.writesVec i
  | .seq a b => xmmFree a && xmmFree b
  | .ite _ a b => xmmFree a && xmmFree b
  | .loop b _ => xmmFree b
  | _ => false

theorem execBlock_xmm : ∀ {is : List Instr} {s s' : State} {t : List Leak},
    is.all (fun i => !KeepReg.writesVec i) = true → execBlock isa is s = some (s', t) → s'.xmm = s.xmm
  | [], s, s', t, _, h => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; rfl
  | i :: is, s, s', t, hw, h => by
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hw
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ h₁
      obtain ⟨p, hp, e⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨rfl, -⟩ := Prod.mk.inj e
      have h₁' : exec i s = some s₁ := h₁
      rw [execBlock_xmm (is := is) (s := s₁) hw.2 hp, KeepReg.exec_xmm hw.1 h₁']

theorem Exec.xmm_free {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') :
    xmmFree c = true → s'.xmm = s.xmm := by
  induction h with
  | block he => intro hc; exact execBlock_xmm hc he
  | seq _ _ ih₁ ih₂ =>
    intro hc; simp only [xmmFree, Bool.and_eq_true] at hc; rw [ih₂ hc.2, ih₁ hc.1]
  | iteT _ _ ih => intro hc; simp only [xmmFree, Bool.and_eq_true] at hc; exact ih hc.1
  | iteF _ _ ih => intro hc; simp only [xmmFree, Bool.and_eq_true] at hc; exact ih hc.2
  | loopExit _ _ ih => intro hc; exact ih hc
  | loopNext _ _ _ ih₁ ih₂ => intro hc; rw [ih₂ hc, ih₁ hc]
  | call => intro hc; simp [xmmFree] at hc
  | frame => intro hc; simp [xmmFree] at hc
  | icall | icallNext => intro hc; simp [xmmFree] at hc

/-- `WP` of such code, and the SSE registers kept. -/
theorem WP.keepX {c : Prog isa} {s : State} {Q : State → Prop} (hc : xmmFree c = true) (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.xmm = s.xmm := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.xmm_free he hc⟩

/-- The key schedule of `R` rounds at `K`, which the state may read. -/
theorem keys_of_perm {K W : Addr} {wn R : Nat} {s : State} (P : PermN K W wn s) (hdi : s.gpr .rdi = K)
    (hR : R = 10 ∨ R = 12 ∨ R = 14) : Keys R (bytesAt s.mem K (16 * (R + 1))) s := by
  have hR14 : R ≤ 14 := by omega_arith
  refine ⟨by rw [hdi], hR14, fun j hj => ?_⟩
  rw [hdi, Proof.Aes.X86_64.AesNi.ofInt_natCast]
  exact P.kR (by omega_arith)

/-- `one`: AES of the block in `xmm0`. -/
theorem one_ok (s : State) {R : Nat} {w : List Byte} (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : Keys R w s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 R) (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * R)) :
    WP isa one s fun s' => rv (s'.xmm .xmm0) = aesWith R w (rv (s.xmm .xmm0)) ∧ XFrame [.xmm8, .xmm0] s s' :=
  WP.mono (aes_ok [.xmm0] (by decide) (by decide) hR s hK hrsi hr10) fun s' ⟨h, f⟩ =>
    ⟨(aesWith_rv (h _ (List.mem_singleton_self _))).symm, f⟩

/-- What `ktop` leaves. -/
structure KtopPost (K W : Addr) (R t : Nat) (nonce : List Byte) (s s' : State) : Prop where
  ktop : blockAtMem s'.mem (W + BitVec.ofNat 64 tmpO) =
    ctxCiph s.mem K R (Proof.Ocb.nonceN t nonce &&& ~~~(63 : Block))
  bot : s'.mem.readW (W + BitVec.ofNat 64 Impl.AesOcb.X86_64.botO) 64 =
    BitVec.ofNat 64 ((Proof.Ocb.nonceN t nonce).extractLsb' 0 6).toNat
  frame : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 Impl.AesOcb.X86_64.botO, 8⟩] s.mem s'.mem
  gpr : ∀ r, r ∉ [Reg.rax, .rcx, .rsi, .rbx, .r12, .r10] → s'.gpr r = s.gpr r
  rsi : s'.gpr .rsi = BitVec.ofNat 64 R
  r10 : s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * R)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `ktop`: `Ktop`, the nonce block with its last 6 bits cleared, enciphered
at `W + tmpO`. -/
theorem ktop_ok {K W SP : Addr} {wn : Nat} (L : LayN K W SP wn) {s : State} (E : EnvN K W SP wn s) {N : Addr}
    {Rn nl t : Nat} (hR : Rn = 10 ∨ Rn = 12 ∨ Rn = 14) (hdi : s.gpr .rdi = K)
    (hrnd : s.mem.readW (W + BitVec.ofNat 64 rndO) 64 = BitVec.ofNat 64 Rn)
    (hN : s.mem.readW (W + BitVec.ofNat 64 Impl.AesOcb.X86_64.nO) 64 = N)
    (hnl : s.mem.readW (W + BitVec.ofNat 64 Impl.AesOcb.X86_64.nlO) 64 = BitVec.ofNat 64 nl)
    (htl : s.mem.readW (W + BitVec.ofNat 64 Impl.AesOcb.X86_64.tlO) 64 = BitVec.ofNat 64 t)
    (h1 : 1 ≤ nl) (h15 : nl ≤ 15) (ht : t < 2 ^ 64) (hB : BufN W SP wn s N nl)
    (hwn : 640 ≤ wn := by decide) (hwlt : wn < 2 ^ 64 := by decide) :
    WP isa ktop s (KtopPost K W Rn t (bytesAt s.mem N nl) s) := by
  have hw : wn < 2 ^ 64 := hwlt
  have eT : tmpO = 112 := rfl
  have eB : Impl.AesOcb.X86_64.botO = 256 := rfl
  have eR : rndO = 232 := rfl
  unfold ktop
  refine WP.seq (WP.mono (keys_ok s (W := W) (R := Rn) E.r15 hrnd (E.perm.wR (by omega_arith) hw))
    fun s₀ ⟨rsi₀, r10₀, g₀, m₀, rd₀, wr₀, x₀⟩ => ?_)
  have E₀ : EnvN K W SP wn s₀ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₀ _ (by decide) (by decide)) rd₀ wr₀
  rw [← m₀] at hN hnl htl
  refine WP.seq (WP.mono (nonceBlock_ok L E₀ hN hnl htl h1 h15 ht (hB.of_eq rd₀ wr₀) hwn hwlt) fun s₁ N₁ => ?_)
  rw [m₀] at N₁
  have E₁ : EnvN K W SP wn s₁ := E₀.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact N₁.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide))
    N₁.rd N₁.wr
  have r10₁ : s₁.gpr .r10 = s₁.gpr .rdi + BitVec.ofNat 64 (16 * Rn) := by
    rw [N₁.gpr .r10 (by decide) (by decide) (by decide) (by decide) (by decide),
      N₁.gpr .rdi (by decide) (by decide) (by decide) (by decide) (by decide), r10₀, g₀ .rdi (by decide) (by decide)]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (keysR_ok s₁ (by omega_arith) r10₁) fun s₂ ⟨rsi₂, g₂, m₂, rd₂, wr₂, x₂⟩ => ?_
  have rT : InRegions (s₂.rd ++ s₂.wr) (W + BitVec.ofNat 64 tmpO) 16 := by
    rw [rd₂, wr₂]; exact E₁.perm.wR (by omega_arith) hw
  have h15₂ : s₂.gpr .r15 = W := by rw [g₂ _ (by decide), E₁.r15]
  rw [show BitVec.ofNat 64 tmpO = 112#64 from rfl] at rT
  apply WP.of_runBlock
  refine ⟨_, by orun [State.load128, h15₂, rT, State.setXmm], ?_⟩
  have hKs : 16 * (Rn + 1) ≤ 256 := by omega_arith
  have sched : bytesAt s₂.mem K (16 * (Rn + 1)) = bytesAt s.mem K (16 * (Rn + 1)) := by
    rw [m₂, Proof.Cmac.bytesAt_frame N₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (L.k_w.sub_left (Region.sub_prefix hKs)).sub_right (LayN.wSub (by omega_arith))
      · exact (L.k_w.sub_left (Region.sub_prefix hKs)).sub_right (LayN.wSub (by omega_arith))) (by omega_arith),
      m₀]
  have keys₂ : Keys Rn (bytesAt s.mem K (16 * (Rn + 1))) s₂ := by
    rw [← sched]
    exact keys_of_perm (E₁.perm.of_eq rd₂ wr₂) (by rw [g₂ _ (by decide), N₁.gpr _ (by decide)
      (by decide) (by decide) (by decide) (by decide), g₀ _ (by decide) (by decide), hdi]) hR
  refine WP.seq (WP.mono (one_ok _ hR (Keys.of_frame (rs := [.xmm0]) keys₂ ⟨rfl, rfl, rfl, rfl, fun r hr => by
      simp only [State.setXmm, List.mem_singleton] at hr ⊢; simp [hr]⟩)
    (by simp only [State.setXmm]; exact rsi₂)
    (by simp only [State.setXmm]; rw [g₂ .r10 (by decide), g₂ .rdi (by decide)]; exact r10₁))
    fun s₄ ⟨v₄, f₄⟩ => ?_)
  have h15₄ : s₄.gpr .r15 = W := by rw [f₄.gpr]; simp only [State.setXmm]; exact h15₂
  have wT : InRegions s₄.wr (W + 112#64) 16 := by
    rw [f₄.wr]; simp only [State.setXmm]; rw [wr₂, N₁.wr, wr₀]
    have := E.perm.wW (d := tmpO) (n := 16) (by omega_arith) hw; rwa [show BitVec.ofNat 64 tmpO = 112#64 from rfl] at this
  apply WP.of_runBlock
  refine ⟨_, by orun [State.store128, h15₄, wT, State.setMem], ?_⟩
  have m₄ : s₄.mem = s₁.mem := by rw [f₄.mem]; simp only [State.setXmm]; exact m₂
  have e112 : W + BitVec.ofNat 64 tmpO = W + 112#64 := rfl
  have fT : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩] s₄.mem (s₄.mem.writeW (W + 112#64) (s₄.xmm .xmm0)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by rw [← e112]; exact Region.contains_self _ _)
  refine ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.setMem, mem_setReg]
  · rw [e112, blockAtMem_writeW, v₄]
    simp only [State.setXmm, ite_true]
    rw [← e112, ← blockAtMem_eq, m₂, N₁.blk]; rfl
  · rw [fT.readW (r := ⟨W + BitVec.ofNat 64 Impl.AesOcb.X86_64.botO, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact LayN.w_w L (.inr (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide), m₄]
    exact N₁.bot
  · rw [m₄] at fT ⊢
    rw [← m₀]
    refine N₁.frame.trans (Frame.mono fT ?_)
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f₄.gpr]; simp only [State.setXmm]
    rw [g₂ r hr.2.2.1, N₁.gpr r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1, g₀ r hr.2.2.1 hr.2.2.2.2.2]
  · rw [f₄.gpr]; simp only [State.setXmm]; exact rsi₂
  · rw [f₄.gpr]; simp only [State.setXmm]
    rw [g₂ .r10 (by decide), N₁.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide), r10₀]
  · rw [f₄.rd]; simp only [State.setXmm]; rw [rd₂, N₁.rd, rd₀]
  · rw [f₄.wr]; simp only [State.setXmm]; rw [wr₂, N₁.wr, wr₀]

/-! ## `HASH` -/

open VG.Proof.Ocb (offAt hsum)

theorem hsum_xorB (ciph : Spec.Ocb.Cipher) (l : Block) (a : List Byte) (m : Nat) :
    hsum ciph l a m = xorB (fun i => ciph (Spec.Ocb.blockAt a i ^^^ offAt 0 l (i + 1))) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [hsum, ih, xorB]

theorem bF_hash (nr : Nat) (w : List Byte) : bF .hash nr w = aesWith nr w := by simp [bF]

theorem bF_seal (nr : Nat) (w : List Byte) : bF .seal nr w = aesWith nr w := by simp [bF]

theorem bF_open (nr : Nat) (w : List Byte) : bF .open nr w = Spec.Ocb.aesInvWith nr w := by simp [bF]

/-- What `hash` needs, at its start: the pass's context over the associated
data (`al` bytes at `A`), and the slots it reads. -/
structure HashPre (s : State) (K W SP A : Addr) (wn R al : Nat) (l : Block) : Prop where
  env : EnvN K W SP wn s
  rdi : s.gpr .rdi = K
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  r10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * R)
  aad : s.mem.readW (W + BitVec.ofNat 64 aadO) 64 = A
  alen : s.mem.readW (W + BitVec.ofNat 64 alenO) 64 = BitVec.ofNat 64 al
  rnd : s.mem.readW (W + BitVec.ofNat 64 rndO) 64 = BitVec.ofNat 64 R
  buf : BufN W SP wn s A al
  kw : (⟨K, 256⟩ : Region).Disjoint ⟨W, wn⟩
  lstar : blockAtMem s.mem (K + 240) = l
  C : ∀ t, 1 ≤ t → t ≤ 7 → blockAtMem s.mem (at' W (cSlot t)) = cAt l t
  L2 : blockAtMem s.mem (at' W l2O) = lAt l 2
  L3 : blockAtMem s.mem (at' W l3O) = lAt l 3
  wnLe : 640 ≤ wn
  wlt : wn < 2 ^ 64

/-- What `hash` writes. -/
abbrev hashW (W : Addr) : List Region :=
  [⟨at' W ofO, 128⟩, ⟨at' W c8O, 16⟩, ⟨at' W ljO, 16⟩, ⟨at' W t2O, 16⟩, ⟨at' W sumO, 16⟩]

/-- What `hash` leaves. -/
structure HashPost (K W : Addr) (R al : Nat) (l : Block) (A : Addr) (s s' : State) : Prop where
  sum : blockAtMem s'.mem (at' W sumO) =
    Spec.Ocb.hash (aesWith R (bytesAt s.mem K (16 * (R + 1)))) l (bytesAt s.mem A al)
  fr : Frame (hashW W) s.mem s'.mem
  gpr : ∀ x, x ∉ [Reg.rax, .rdx, .rcx, .r8, .r9, .r11, .r12, .r13, .rbx, .rsi] → s'.gpr x = s.gpr x
  rsi : s'.gpr .rsi = BitVec.ofNat 64 R
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem pxor_self (x : BitVec 128) : XBinOp.eval .pxor x x = 0 := by simp [XBinOp.eval]

/-- `hash`'s first block. -/
theorem hash1_ok {s : State} {K W SP A : Addr} {wn R al : Nat} {l : Block} (H : HashPre s K W SP A wn R al l) :
    ∃ s₁, runBlock isa [ld .r11 .r15 aadO, ld .r12 .r15 alenO, .shift .shr .r12 4, .xop (.bin .pxor .xmm12 .xmm12),
        .xop (.bin .pxor .xmm10 .xmm10)] s = some s₁ ∧
      s₁.gpr .r11 = A ∧ s₁.gpr .r12 = BitVec.ofNat 64 (al / 16) ∧ s₁.xmm .xmm12 = 0 ∧ s₁.xmm .xmm10 = 0 ∧
      (∀ x, x ≠ .r11 → x ≠ .r12 → s₁.gpr x = s.gpr x) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      (∀ x, x ≠ .xmm12 → x ≠ .xmm10 → s₁.xmm x = s.xmm x) := by
  have hw := H.wlt
  have hwn := H.wnLe
  have rA : InRegions (s.rd ++ s.wr) (W + 240#64) 8 :=
    H.env.perm.wR (d := aadO) (n := 8) (by simp only [aadO]; omega_arith) hw
  have rL : InRegions (s.rd ++ s.wr) (W + 248#64) 8 :=
    H.env.perm.wR (d := alenO) (n := 8) (by simp only [alenO]; omega_arith) hw
  have hA : s.mem.readW (W + 240#64) 64 = A := H.aad
  have hL : s.mem.readW (W + 248#64) 64 = BitVec.ofNat 64 al := H.alen
  have hal : al < 2 ^ 64 := H.buf.lt
  refine ⟨_, by orun [H.env.r15, rA, rL, hA, hL, XOp.exec, State.setXmm], ?_, ?_, ?_, ?_, fun x h1 h2 => ?_, ?_, ?_, ?_,
    fun x h1 h2 => ?_⟩
  · simp only [gpr_setReg, gpr_setFlags, State.setXmm, ite_true, reduceCtorEq, ite_false]
  · simp only [gpr_setReg, gpr_setFlags, State.setXmm, ite_true, reduceCtorEq, ite_false, shr4 al hal]
  · simp [State.setXmm, pxor_self]
  · simp [State.setXmm, pxor_self]
  · simp only [gpr_setReg, gpr_setFlags, State.setXmm, h1, h2, ite_false]
  · simp [State.setXmm, mem_setReg, mem_setFlags]
  · simp [State.setXmm, rd_setReg, rd_setFlags]
  · simp [State.setXmm, wr_setReg, wr_setFlags]
  · simp [State.setXmm, xmm_setReg, xmm_setFlags, h1, h2]

/-- `hash`: `HASH(K, A)` to `W + sumO`. -/
theorem hash_ok {s : State} {K W SP A : Addr} {wn R al : Nat} {l : Block} (H : HashPre s K W SP A wn R al l) :
    WP isa Impl.AesOcb.X86_64AesNi.hash s (HashPost K W R al l A s) := by
  have hw := H.wlt
  have hwn := H.wnLe
  have hal : al < 2 ^ 64 := H.buf.lt
  have hR14 : 16 * (R + 1) ≤ 240 := by rcases H.rounds with h | h | h <;> omega_arith
  obtain ⟨s₁, run₁, r11₁, r12₁, x12₁, x10₁, g₁, m₁, rd₁, wr₁, xo₁⟩ := hash1_ok H
  unfold Impl.AesOcb.X86_64AesNi.hash
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have rdi₁ : s₁.gpr .rdi = K := by rw [g₁ _ (by decide) (by decide), H.rdi]
  have P : PCtx .hash s₁ A W wn R (bytesAt s.mem K (16 * (R + 1))) l (al / 16) := {
    nrOk := H.rounds
    keys := by
      have := keys_of_perm (H.env.perm.of_eq rd₁ wr₁) rdi₁ H.rounds
      rwa [m₁] at this
    rsi := by rw [g₁ _ (by decide) (by decide), H.rsi]
    r10 := by rw [g₁ _ (by decide) (by decide), g₁ _ (by decide) (by decide), H.r10]
    imc := fun h => absurd h (by decide)
    r15 := by rw [g₁ _ (by decide) (by decide), H.env.r15]
    wnLe := hwn
    wno := fun h => absurd h (by decide)
    w64 := hw
    m64 := by omega_arith
    D := by rw [rd₁, wr₁]; exact Proof.AesOcb.X86_64.covers_prefix H.buf.rd (by omega_arith)
    Dw := fun h => absurd rfl h
    wcov := by rw [wr₁]; exact H.env.perm.w
    DW := H.buf.w.sub_left (Region.sub_prefix (by omega_arith))
    KW := by rw [rdi₁]; exact H.kw.sub_left (Region.sub_prefix (by decide))
    KD := fun h => absurd rfl h
    C := fun t h1 h7 => by rw [m₁]; exact H.C t h1 h7
    L2 := by rw [m₁]; exact H.L2
    L3 := by rw [m₁]; exact H.L3 }
  refine WP.seq (WP.mono (pass_ok P (o0 := 0) r12₁ r11₁ (by rw [x12₁]; exact rv_zero)) fun s₂ Q₂ => ?_)
  -- The memory outside what the pass wrote is `s`'s.
  have keepW : ∀ {d : Nat}, d + 8 ≤ ljO → s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun {d} hd => by
      have e1 : ofO = 512 := rfl
      have e2 : c8O = 496 := rfl
      have e3 : ljO = 336 := rfl
      have e4 : cO = 384 := rfl
      rw [Q₂.fr.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [passW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, ↓reduceIte,
          List.nil_append] at hr
        rcases hr with rfl | rfl | rfl
        all_goals exact Offset.disjoint W (.inl (by omega_arith)) (by omega_arith) (by omega_arith)) (by decide), m₁]
  have hL₂ : s₂.mem.readW (W + 248#64) 64 = BitVec.ofNat 64 al := by
    have := keepW (d := alenO) (by decide)
    rw [show (248#64 : BitVec 64) = BitVec.ofNat 64 alenO from rfl, this]; exact H.alen
  have rL₂ : InRegions (s₂.rd ++ s₂.wr) (W + 248#64) 8 := by
    rw [Q₂.rd, Q₂.wr, rd₁, wr₁]; exact H.env.perm.wR (d := alenO) (n := 8) (by simp only [alenO]; omega_arith) hw
  have h15₂ : s₂.gpr .r15 = W := by rw [Q₂.gpr _ (by decide), P.r15]
  obtain ⟨s₃, run₃, rbx₃, r12₃, zf₃, g₃, m₃, rd₃, wr₃, x₃⟩ : ∃ s₃, runBlock isa
      [Impl.AesOcb.X86_64.mvr .rbx .r11, ld .r12 .r15 alenO, .alu .and .r12 (.imm 15)] s₂ = some s₃ ∧
      s₃.gpr .rbx = A + BitVec.ofNat 64 (16 * (al / 16)) ∧ s₃.gpr .r12 = BitVec.ofNat 64 (al % 16) ∧
      s₃.zf = some (decide (al % 16 = 0)) ∧ (∀ x, x ≠ .rbx → x ≠ .r12 → s₃.gpr x = s₂.gpr x) ∧ s₃.mem = s₂.mem ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr ∧ s₃.xmm = s₂.xmm := by
    have e15 : BitVec.signExtend 64 (15 : BitVec 32) = 15#64 := by decide
    have ea : BitVec.ofNat 64 al &&& 15#64 = BitVec.ofNat 64 (al % 16) := by
      rw [and15', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hal]
    refine ⟨_, by orun [h15₂, hL₂, rL₂], ?_, ?_, ?_, fun x h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, reduceCtorEq, ite_false, Q₂.r11]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, reduceCtorEq, ite_false, e15, ea]
    · simp only [zf_setReg, zf_arithFlags, zf_setFlags, gpr_setReg, gpr_arithFlags, ite_true, reduceCtorEq,
        ite_false, e15, ea]
      by_cases h : al % 16 = 0
      · simp [h]
      · have : BitVec.ofNat 64 (al % 16) ≠ 0#64 := fun h' => h (by
          have := congrArg BitVec.toNat h'
          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this)
        simp [h, this]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h1, h2, ite_false]
    all_goals simp only [mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg,
      wr_arithFlags, wr_setFlags, xmm_setReg, xmm_arithFlags, xmm_setFlags]
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  -- What the pass computed, as `HASH` needs it.
  have hlenA : (bytesAt s.mem A al).length = al := Proof.AesCcm.X86_64.length_bytesAt _ _ _
  have hX : rv (s₃.xmm .xmm10) = hsum (aesWith R (bytesAt s.mem K (16 * (R + 1)))) l (bytesAt s.mem A al) (al / 16) := by
    rw [x₃, Q₂.x10, x10₁, rv_zero, show ∀ x : Block, (0 : Block) ^^^ x = x from fun x => by simp, hsum_xorB]
    refine xorB_congr fun i hi => ?_
    simp only [termB, term, bF_hash, m₁]
    rw [Proof.Ocb.blockAt_bytesAt _ _ (by omega_arith)]
  have hO : rv (s₃.xmm .xmm12) = offAt 0 l (al / 16) := by rw [x₃, Q₂.x12]
  have E₃ : EnvN K W SP wn s₃ := H.env.keep (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      all_goals rw [g₃ _ (by decide) (by decide), Q₂.gpr _ (by decide), g₁ _ (by decide) (by decide)])
    (by rw [rd₃, Q₂.rd, rd₁]) (by rw [wr₃, Q₂.wr, wr₁])
  have rsi₃ : s₃.gpr .rsi = BitVec.ofNat 64 R := by rw [g₃ _ (by decide) (by decide), Q₂.gpr _ (by decide), P.rsi]
  have rdi₃ : s₃.gpr .rdi = K := by rw [g₃ _ (by decide) (by decide), Q₂.gpr _ (by decide), rdi₁]
  -- The memory of the key context and the associated data is `s`'s.
  have aadKeep : ∀ {d n : Nat}, d + n ≤ al →
      bytesAt s₃.mem (A + BitVec.ofNat 64 d) n = bytesAt s.mem (A + BitVec.ofNat 64 d) n := fun {d n} hdn => by
    rw [m₃, Proof.AesCcm.X86_64.bytesAt_frame Q₂.fr (fun r hr => by
      have hAW := H.buf.w.sub_left (Offset.sub_base A hdn)
      simp only [passW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, ↓reduceIte,
        List.nil_append] at hr
      rcases hr with rfl | rfl | rfl
      all_goals exact hAW.sub_right (Offset.sub_base W (by simp only [ofO, c8O, cO, ljO]; omega_arith)))
      (by omega_arith), m₁]
  have hash_eq' := Proof.Ocb.hash_eq (aesWith R (bytesAt s.mem K (16 * (R + 1)))) l (bytesAt s.mem A al)
  rw [hlenA, Proof.Ocb.bytesAt_drop _ _ (by omega_arith), Proof.AesCcm.X86_64.length_bytesAt] at hash_eq'
  have mid : WP isa (.ite .e (.block [])
      (.seq (padTo t2O) (.seq (.block ([.movdquLoad .xmm11 (at_ .rdi 240), .xop (.bin .pxor .xmm12 .xmm11),
          .movdquLoad .xmm0 (at_ .r15 t2O), .xop (.bin .pxor .xmm0 .xmm12)] ++ keysR))
        (.seq one (.block [.xop (.bin .pxor .xmm10 .xmm0)]))))) s₃ fun s₄ =>
      rv (s₄.xmm .xmm10) = Spec.Ocb.hash (aesWith R (bytesAt s.mem K (16 * (R + 1)))) l (bytesAt s.mem A al) ∧
      s₄.gpr .r15 = W ∧ Frame [⟨at' W t2O, 16⟩] s₃.mem s₄.mem ∧
      (∀ x, x ∉ [Reg.rax, .rcx, .rsi] → s₄.gpr x = s₃.gpr x) ∧ s₄.gpr .rsi = BitVec.ofNat 64 R ∧
      s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr := by
    by_cases hr : al % 16 = 0
    · refine WP.ite true (by simp [isa, eval, zf₃, hr]) (fun _ => WP.block_nil ⟨?_, E₃.r15, Frame.refl _ _,
        fun _ _ => rfl, rsi₃, rfl, rfl⟩) (fun h => absurd h (by decide))
      rw [hash_eq', hX]; simp only [show ¬ (al - 16 * (al / 16) > 0) by omega_arith, ↓reduceIte]
    · refine WP.ite false (by simp [isa, eval, zf₃, hr]) (fun h => absurd h (by decide)) fun _ => ?_
      have hr0 : 0 < al % 16 := by omega_arith
      have e128 : t2O = 128 := rfl
      have e232 : rndO = 232 := rfl
      refine WP.seq (WP.mono (WP.keepX (c := padTo t2O) (by decide)
        (padTo_ok E₃ (S := A + BitVec.ofNat 64 (16 * (al / 16))) (n := al % 16) (d := t2O) hr0 (by omega_arith)
          (by decide) rbx₃ r12₃
          (by rw [rd₃, Q₂.rd, rd₁, wr₃, Q₂.wr, wr₁]; exact Proof.AesCcm.X86_64.covers_off H.buf.rd (by omega_arith) hal)
          ((H.buf.w.sub_left (Offset.sub_base A (by omega_arith))).sub_right (LayN.wSub (by omega_arith)))
          hwn hw)) fun s₅ ⟨⟨fr₅, pad₅, g₅, rd₅, wr₅⟩, x₅⟩ => ?_)
      have g₅' : ∀ x, x ∉ [Reg.rax, .rcx, .rsi] → s₅.gpr x = s₃.gpr x := fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        exact g₅ x hx.1 hx.2.1 hx.2.2
      have h15₅ : s₅.gpr .r15 = W := by rw [g₅' _ (by decide), E₃.r15]
      have rdi₅ : s₅.gpr .rdi = K := by rw [g₅' _ (by decide), rdi₃]
      have rK : InRegions (s₅.rd ++ s₅.wr) (K + 240#64) 16 := by
        rw [rd₅, wr₅]; exact E₃.perm.kR (d := 240) (n := 16) (by decide)
      have rT : InRegions (s₅.rd ++ s₅.wr) (W + 128#64) 16 := by
        rw [rd₅, wr₅]; exact E₃.perm.wR (d := t2O) (n := 16) (by omega_arith) hw
      refine WP.seq ?_
      rw [WP.block_append_iff]
      apply WP.of_runBlock
      refine ⟨_, by orun [rdi₅, h15₅, rK, rT, State.load128, XOp.exec, State.setXmm], ?_⟩
      -- What `s₅` keeps of `s`.
      have mKW : ∀ {p : Addr} {n : Nat}, (⟨p, n⟩ : Region).Disjoint ⟨W, wn⟩ → n ≤ 256 →
          bytesAt s₅.mem p n = bytesAt s.mem p n := fun {p n} hp hn => by
        rw [Proof.AesCcm.X86_64.bytesAt_frame fr₅ (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact hp.sub_right (LayN.wSub (by omega_arith)))
            (by omega_arith), m₃,
          Proof.AesCcm.X86_64.bytesAt_frame Q₂.fr (fun r hr => by
            simp only [passW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, ↓reduceIte,
              List.nil_append] at hr
            rcases hr with rfl | rfl | rfl
            all_goals exact hp.sub_right (Offset.sub_base W (by simp only [ofO, c8O, cO, ljO]; omega_arith)))
            (by omega_arith), m₁]
      have sched₅ : bytesAt s₅.mem K (16 * (R + 1)) = bytesAt s.mem K (16 * (R + 1)) :=
        mKW (H.kw.sub_left (Region.sub_prefix (by omega_arith))) (by omega_arith)
      have lstar₅ : blockAtMem s₅.mem (K + 240) = l := by
        rw [blockAtMem, show (K + 240 : Addr) = K + BitVec.ofNat 64 240 from rfl,
          mKW (H.kw.sub_left (Offset.sub_base K (by decide))) (by decide)]
        exact H.lstar
      have r10₅ : s₅.gpr .r10 = s₅.gpr .rdi + BitVec.ofNat 64 (16 * R) := by
        rw [g₅' .r10 (by decide), g₅' .rdi (by decide), g₃ .r10 (by decide) (by decide),
          g₃ .rdi (by decide) (by decide), Q₂.gpr .r10 (by decide), Q₂.gpr .rdi (by decide),
          g₁ .r10 (by decide) (by decide), g₁ .rdi (by decide) (by decide)]
        exact H.r10
      refine WP.mono (keysR_ok _ (R := R) (by rcases H.rounds with h | h | h <;> omega_arith)
        (by simp only [State.setXmm]; exact r10₅))
        fun s₇ ⟨rsi₇, g₇, m₇, rd₇, wr₇, x₇⟩ => ?_
      simp only [State.setXmm] at g₇ m₇ rd₇ wr₇ x₇
      have rdi₇ : s₇.gpr .rdi = K := by rw [g₇ _ (by decide), rdi₅]
      have keys₇ : Keys R (bytesAt s.mem K (16 * (R + 1))) s₇ := by
        have := keys_of_perm (E₃.perm.of_eq (rd₇.trans rd₅) (wr₇.trans wr₅)) rdi₇ H.rounds
        rwa [m₇, sched₅] at this
      have r10₇ : s₇.gpr .r10 = s₇.gpr .rdi + BitVec.ofNat 64 (16 * R) := by
        rw [g₇ .r10 (by decide), g₇ .rdi (by decide)]; exact r10₅
      refine WP.seq (WP.mono (one_ok s₇ H.rounds keys₇ rsi₇ r10₇) fun s₈ ⟨v₈, f₈⟩ => ?_)
      apply WP.of_runBlock
      refine ⟨_, by orun [XOp.exec, State.setXmm], ?_⟩
      have hpx : ∀ a b : BitVec 128, XBinOp.eval .pxor a b = a ^^^ b := fun _ _ => rfl
      have hx0 : rv (s₇.xmm .xmm0) = Spec.Ocb.pad (bytesAt s.mem (A + BitVec.ofNat 64 (16 * (al / 16)))
          (al - 16 * (al / 16))) ^^^ (offAt 0 l (al / 16) ^^^ l) := by
        rw [x₇]
        simp only [ite_true, reduceCtorEq, ite_false]
        rw [hpx, hpx, rv_xor, rv_xor, ← blockAtMem_eq, ← blockAtMem_eq, x₅, hO,
          show W + 128#64 = W + BitVec.ofNat 64 t2O from rfl, pad₅, show (K + 240#64 : Addr) = K + 240 from rfl,
          lstar₅, aadKeep (by omega_arith), show al - 16 * (al / 16) = al % 16 by omega_arith]
      have hx10 : rv (s₇.xmm .xmm10) = rv (s₃.xmm .xmm10) := by
        rw [x₇]; simp only [reduceCtorEq, ite_false]; rw [x₅]
      refine ⟨?_, ?_, ?_, fun x hx => ?_, ?_, ?_, ?_⟩
      · simp only [State.setXmm, ite_true]
        rw [hpx, rv_xor, v₈, f₈.xmm .xmm10 (by decide), hx10, hx0, hX, hash_eq']
        simp only [show al - 16 * (al / 16) > 0 by omega_arith, ↓reduceIte]
      · simp only [State.setXmm]; rw [f₈.gpr, g₇ _ (by decide), h15₅]
      · simp only [State.setXmm]; rw [f₈.mem, m₇]; exact fr₅
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        simp only [State.setXmm]
        rw [f₈.gpr, g₇ x hx.2.2, g₅' x (by simp [hx.1, hx.2.1, hx.2.2])]
      · simp only [State.setXmm]; rw [f₈.gpr]; exact rsi₇
      · simp only [State.setXmm]; rw [f₈.rd, rd₇, rd₅]
      · simp only [State.setXmm]; rw [f₈.wr, wr₇, wr₅]
  refine WP.seq (WP.mono mid fun s₄ ⟨x10₄, h15₄, fr₄, g₄, rsi₄, rd₄, wr₄⟩ => ?_)
  have wS : InRegions s₄.wr (W + 48#64) 16 := by
    rw [wr₄, wr₃, Q₂.wr, wr₁]; exact H.env.perm.wW (d := sumO) (n := 16) (by simp only [sumO]; omega_arith) hw
  apply WP.of_runBlock
  refine ⟨_, by orun [State.store128, h15₄, wS, State.setMem], ?_⟩
  exact {
    sum := by
      simp only [State.setMem]
      rw [show at' W sumO = W + 48#64 from rfl, blockAtMem_writeW, x10₄]
    fr := by
      simp only [State.setMem]
      have inH : ∀ r ∈ passW .hash W A (al / 16), ∃ r' ∈ hashW W, r.Sub r' := fun r hr => by
        simp only [passW, List.mem_append, reduceCtorEq, ↓reduceIte, List.not_mem_nil, or_false, List.mem_cons] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
      have inT : (⟨at' W t2O, 16⟩ : Region) ∈ hashW W :=
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      have inS : (⟨at' W sumO, 16⟩ : Region) ∈ hashW W :=
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_self ..))))
      have f1 : Frame (hashW W) s.mem s₂.mem := by rw [← m₁]; exact Frame.sub Q₂.fr inH
      have f2 : Frame (hashW W) s₂.mem s₄.mem := by
        rw [← m₃]; exact Frame.sub fr₄ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, inT, fun _ h => h⟩
      exact (f1.trans f2).writeW inS _ (Region.contains_self _ _)
    gpr := fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp only [State.setMem]
      rw [g₄ x (by simp [hx.1, hx.2.2.1, hx.2.2.2.2.2.2.2.2.2]),
        g₃ x hx.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.1, Q₂.gpr x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1,
          hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.1]),
        g₁ x hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1]
    rsi := by simp only [State.setMem]; exact rsi₄
    rd := by simp only [State.setMem]; rw [rd₄, rd₃, Q₂.rd, rd₁]
    wr := by simp only [State.setMem]; rw [wr₄, wr₃, Q₂.wr, wr₁] }

/-! ## `Offset_0` -/

/-- What `nonce` leaves. -/
structure NoncePostF (W : Addr) (R : Nat) (o : Block) (s s' : State) : Prop where
  x12 : rv (s'.xmm .xmm12) = o
  x10 : s'.xmm .xmm10 = 0
  fr : Frame [⟨W + BitVec.ofNat 64 Impl.AesOcb.X86_64.ofsO, 16⟩, ⟨W + BitVec.ofNat 64 Impl.AesOcb.X86_64.o0O, 16⟩]
    s.mem s'.mem
  gpr : ∀ r, r ∉ [Reg.rax, .rdx, .rcx, .rbx, .r8, .r9, .r10, .r11, .rsi] → s'.gpr r = s.gpr r
  rsi : s'.gpr .rsi = BitVec.ofNat 64 R
  r10 : s'.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * R)
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `nonce`: `Offset_0` to `xmm12`, from `Ktop` at `W + tmpO` and `bottom` at
`W + botO`, and `xmm10 ← 0`. -/
theorem nonce_ok {K W SP : Addr} {wn : Nat} (L : LayN K W SP wn) {s : State} (E : EnvN K W SP wn s) {R t : Nat}
    {nb : List Byte} (ciph : Spec.Ocb.Cipher)
    (hktop : blockAtMem s.mem (W + BitVec.ofNat 64 tmpO) = ciph (Proof.Ocb.nonceN t nb &&& ~~~(63 : Block)))
    (hbot : s.mem.readW (W + BitVec.ofNat 64 Impl.AesOcb.X86_64.botO) 64 =
      BitVec.ofNat 64 ((Proof.Ocb.nonceN t nb).extractLsb' 0 6).toNat)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 R)
    (hwn : 640 ≤ wn := by decide) (hwlt : wn < 2 ^ 64 := by decide) :
    WP isa (.block nonce) s (NoncePostF W R (Spec.Ocb.offset0 ciph t nb) s) := by
  have hw : wn < 2 ^ 64 := hwlt
  have hbv : ((Proof.Ocb.nonceN t nb).extractLsb' 0 6).toNat < 64 := (BitVec.extractLsb' 0 6 _).isLt
  obtain ⟨s₁, run₁, P₁⟩ := offset0_ok L E hbv hbot hwn hwlt
  unfold nonce
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  have g₁ : ∀ r, r ∉ [Reg.rax, .rdx, .rcx, .rbx, .r8, .r9, .r10, .r11] → s₁.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact P₁.gpr r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2
  have h15₁ : s₁.gpr .r15 = W := by rw [g₁ _ (by decide), E.r15]
  rw [WP.block_append_iff]
  refine WP.mono (lastKey_ok s₁ (R := R) (by rw [g₁ _ (by decide), hsi])) fun s₂ ⟨r10₂, g₂, m₂, rd₂, wr₂, x₂⟩ => ?_
  rw [WP.block_append_iff]
  have h15₂ : s₂.gpr .r15 = W := by rw [g₂ _ (by decide), h15₁]
  refine WP.mono (ldx_ok .xmm12 .xmm11 Impl.AesOcb.X86_64.ofsO s₂ h15₂ (by decide)
    (by rw [rd₂, wr₂, P₁.rd, P₁.wr]; exact E.perm.wR (by simp only [Impl.AesOcb.X86_64.ofsO]; omega_arith) hw)
    (by rw [rd₂, wr₂, P₁.rd, P₁.wr]; exact E.perm.wR (by simp only [Impl.AesOcb.X86_64.ofsO]; omega_arith) hw))
    fun s₃ ⟨v₃, g₃, m₃, rd₃, wr₃, x₃⟩ => ?_
  apply WP.of_runBlock
  refine ⟨_, by orun [XOp.exec, State.setXmm], ?_⟩
  refine ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.setXmm, reduceCtorEq, ite_false]
    rw [v₃, m₂, ← blockAtMem_eq, P₁.ofs, hktop, Proof.Ocb.offset0_eq]; rfl
  · simp [State.setXmm, pxor_self]
  · simp only [State.setXmm]; rw [m₃, m₂]; exact P₁.frame
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [State.setXmm]
    rw [g₃ r hr.1 hr.2.1, g₂ r hr.2.2.2.2.2.2.1,
      g₁ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.1])]
  · simp only [State.setXmm]; rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), g₁ _ (by decide)]; exact hsi
  · simp only [State.setXmm]; rw [g₃ _ (by decide) (by decide), r10₂, g₁ _ (by decide)]
  · simp only [State.setXmm]; rw [rd₃, rd₂, P₁.rd]
  · simp only [State.setXmm]; rw [wr₃, wr₂, P₁.wr]

/-! ## The rest of the data -/

/-- What `rest` needs: the data's last `r` bytes at `P`, the offset `o` in
`xmm12` and the checksum `c` in `xmm10`. -/
structure RestPre (s : State) (K W SP P : Addr) (wn R r : Nat) (l o c : Block) : Prop where
  env : EnvN K W SP wn s
  rdi : s.gpr .rdi = K
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  r10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * R)
  rbx : s.gpr .rbx = P
  r12 : s.gpr .r12 = BitVec.ofNat 64 r
  r0 : 0 < r
  r16 : r < 16
  buf : DBufN K W SP wn s P r
  lstar : blockAtMem s.mem (K + 240) = l
  x12 : rv (s.xmm .xmm12) = o
  x10 : rv (s.xmm .xmm10) = c
  wnLe : 640 ≤ wn
  wlt : wn < 2 ^ 64

/-- What `rest` leaves: the data XORed with `Pad = ENCIPHER(K, o ⊕ L_*)`, the
offset `o ⊕ L_*`, and the checksum with the padded plaintext. -/
structure RestPost (enc : Bool) (K W P : Addr) (R r : Nat) (l o c : Block) (s s' : State) : Prop where
  data : bytesAt s'.mem P r = Spec.Ocb.xor (bytesAt s.mem P r)
    (Spec.Ocb.toBytes (aesWith R (bytesAt s.mem K (16 * (R + 1))) (o ^^^ l)))
  x12 : rv (s'.xmm .xmm12) = o ^^^ l
  x10 : rv (s'.xmm .xmm10) = c ^^^ Spec.Ocb.pad (if enc then bytesAt s.mem P r else bytesAt s'.mem P r)
  fr : Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩, ⟨W + BitVec.ofNat 64 t2O, 16⟩, ⟨P, r⟩] s.mem s'.mem
  gpr : ∀ x, x ∉ [Reg.rax, .rdx, .rcx, .rsi] → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem xor_take_eq : ∀ (a b : List Byte) {n : Nat}, a.length ≤ n → Spec.Ocb.xor a (b.take n) = Spec.Ocb.xor a b
  | [], _, _, _ => by simp [Spec.Ocb.xor]
  | x :: a, [], n, _ => by simp [Spec.Ocb.xor]
  | x :: a, y :: b, n + 1, h => by
    simp only [Spec.Ocb.xor, List.take_succ_cons, List.zipWith_cons_cons, List.cons.injEq, true_and]
    exact xor_take_eq a b (by simp at h; omega_arith)
  | _ :: _, _ :: _, 0, h => by simp at h

/-- The first `t ≤ 16` bytes of a block. -/
theorem bytesAt_take_block (m : Mem) (p : Addr) {t : Nat} (h : t ≤ 16) :
    bytesAt m p t = (Spec.Ocb.toBytes (blockAtMem m p)).take t := by
  rw [blockAtMem, Proof.Ocb.toBytes_ofBytes (Proof.AesCcm.X86_64.length_bytesAt _ _ _),
    show (16 : Nat) = t + (16 - t) by omega_arith, Proof.Ocb.bytesAt_append,
    List.take_left' (Proof.AesCcm.X86_64.length_bytesAt _ _ _)]

/-- The pad's block (`ENCIPHER` of `o ⊕ L_*`) to `xmm0` and `W + tmpO`. -/
theorem restHead_ok {s : State} {K W SP P : Addr} {wn R r : Nat} {l o c : Block}
    (H : RestPre s K W SP P wn R r l o c) :
    WP isa Impl.AesOcb.X86_64AesNi.restHead s fun s' =>
      blockAtMem s'.mem (W + BitVec.ofNat 64 tmpO) = aesWith R (bytesAt s.mem K (16 * (R + 1))) (o ^^^ l) ∧
      rv (s'.xmm .xmm12) = o ^^^ l ∧ rv (s'.xmm .xmm10) = c ∧
      Frame [⟨W + BitVec.ofNat 64 tmpO, 16⟩] s.mem s'.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hw := H.wlt
  have rK : InRegions (s.rd ++ s.wr) (K + 240#64) 16 := H.env.perm.kR (d := 240) (n := 16) (by decide)
  rw [← H.rdi] at rK
  unfold Impl.AesOcb.X86_64AesNi.restHead
  apply WP.seq
  apply WP.of_runBlock
  refine ⟨_, by orun [rK, State.load128, XOp.exec, State.setXmm], ?_⟩
  have hpx : ∀ a b : BitVec 128, XBinOp.eval .pxor a b = a ^^^ b := fun _ _ => rfl
  have hmv : ∀ a b : BitVec 128, XBinOp.eval .movdqa a b = b := fun _ _ => rfl
  refine WP.seq (WP.mono (one_ok _ H.rounds (Keys.of_frame (rs := [.xmm11, .xmm12, .xmm0])
      (keys_of_perm H.env.perm H.rdi H.rounds) ⟨rfl, rfl, rfl, rfl, fun x hx => by
        simp only [State.setXmm, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx ⊢
        simp [hx.1, hx.2.1, hx.2.2]⟩)
    (by simp only [State.setXmm]; exact H.rsi) (by simp only [State.setXmm]; exact H.r10)) fun s₂ ⟨v₂, f₂⟩ => ?_)
  have h15₂ : s₂.gpr .r15 = W := by rw [f₂.gpr]; simp only [State.setXmm]; exact H.env.r15
  have wT : InRegions s₂.wr (W + 112#64) 16 := by
    have := H.wnLe
    rw [f₂.wr]; simp only [State.setXmm]; exact H.env.perm.wW (d := tmpO) (n := 16) (by simp only [tmpO]; omega_arith) hw
  apply WP.of_runBlock
  refine ⟨_, by orun [State.store128, h15₂, wT, State.setMem], ?_⟩
  have x12v : rv (XBinOp.eval .pxor (s.xmm .xmm12) (s.mem.readW (s.gpr .rdi + 240#64) 128)) = o ^^^ l := by
    rw [hpx, rv_xor, H.x12, ← blockAtMem_eq, H.rdi]; rw [← H.lstar]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.setMem]
  · rw [show W + BitVec.ofNat 64 tmpO = W + 112#64 from rfl, blockAtMem_writeW, v₂]
    simp only [State.setXmm, ite_true, hmv, reduceCtorEq, ite_false]
    rw [x12v]
  · rw [f₂.xmm _ (by decide)]; simp only [State.setXmm, ite_true, reduceCtorEq, ite_false]; exact x12v
  · rw [f₂.xmm _ (by decide)]; simp only [State.setXmm, reduceCtorEq, ite_false]; exact H.x10
  · rw [f₂.mem]; simp only [State.setXmm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [f₂.gpr]
  · rw [f₂.rd]
  · rw [f₂.wr]

theorem addPad_ok (s : State) {W : Addr} (h15 : s.gpr .r15 = W) (rT : InRegions (s.rd ++ s.wr) (W + 128#64) 16) :
    WP isa (.block addPad) s fun s' =>
      s'.xmm .xmm10 = s.xmm .xmm10 ^^^ s.mem.readW (W + BitVec.ofNat 64 t2O) 128 ∧ s'.gpr = s.gpr ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ x, x ≠ .xmm10 → x ≠ .xmm11 → s'.xmm x = s.xmm x) := by
  apply WP.of_runBlock
  refine ⟨_, by orun [addPad, h15, rT, State.load128, XOp.exec, State.setXmm], ?_⟩
  refine ⟨by simp [State.setXmm, XBinOp.eval]; rfl, rfl, rfl, rfl, rfl, fun x h1 h2 => by simp [State.setXmm, h1, h2]⟩

/-- `rest`. -/
theorem rest_ok (enc : Bool) {s : State} {K W SP P : Addr} {wn R r : Nat} {l o c : Block}
    (H : RestPre s K W SP P wn R r l o c) :
    WP isa (rest enc) s (RestPost enc K W P R r l o c s) := by
  have hw := H.wlt
  have hwn := H.wnLe
  have hr16 := H.r16
  have hr0 := H.r0
  have hPW : (⟨P, r⟩ : Region).Disjoint ⟨W, wn⟩ := H.buf.w
  have e112 : tmpO = 112 := rfl
  have e128 : t2O = 128 := rfl
  unfold rest
  refine WP.seq (WP.mono (restHead_ok H) fun s₁ ⟨pad₁, x12₁, x10₁, fr₁, g₁, rd₁, wr₁⟩ => ?_)
  have E₁ : EnvN K W SP wn s₁ := H.env.keep (fun x _ => by rw [g₁]) rd₁ wr₁
  have B₁ : DBufN K W SP wn s₁ P r := H.buf.of_eq rd₁ wr₁
  have hPT : ∀ {d : Nat}, d + 16 ≤ wn → (⟨P, r⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 d, 16⟩ := fun hd =>
    hPW.sub_right (LayN.wSub hd)
  have keepP₁ : bytesAt s₁.mem P r = bytesAt s.mem P r :=
    Proof.AesCcm.X86_64.bytesAt_frame fr₁ (fun q hq => by
      simp only [List.mem_singleton] at hq; subst hq; exact hPT (by omega_arith)) (by omega_arith)
  have rT : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr → InRegions (t.rd ++ t.wr) (W + 128#64) 16 := fun h1 h2 => by
    rw [h1, h2]; exact H.env.perm.wR (d := t2O) (n := 16) (by omega_arith) hw
  -- The pad's bytes at `W + tmpO`, after a frame that misses them.
  have padBytes : ∀ {m : Mem}, Frame [⟨W + BitVec.ofNat 64 t2O, 16⟩] s₁.mem m →
      bytesAt m (W + BitVec.ofNat 64 112) r =
        (Spec.Ocb.toBytes (aesWith R (bytesAt s.mem K (16 * (R + 1))) (o ^^^ l))).take r := fun {m} hf => by
    rw [bytesAt_take_block _ _ (by omega_arith), show W + BitVec.ofNat 64 112 = W + BitVec.ofNat 64 tmpO from rfl,
      Proof.Ocb.blockAtMem_frame hf (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq
        exact Offset.disjoint W (.inl (by decide)) (by omega_arith) (by omega_arith)), pad₁]
  have keepP : ∀ {m : Mem}, Frame [⟨W + BitVec.ofNat 64 t2O, 16⟩] s₁.mem m → bytesAt m P r = bytesAt s.mem P r :=
    fun {m} hf => by
      rw [Proof.AesCcm.X86_64.bytesAt_frame hf (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hPT (by omega_arith)) (by omega_arith), keepP₁]
  have hlen : ∀ (m : Mem) (q : Addr), (Spec.Ocb.xor (bytesAt m P r) (bytesAt m q r)).length = r := fun m q =>
    by simp [Spec.Ocb.xor, Proof.AesCcm.X86_64.length_bytesAt]
  cases enc
  · -- `open`: the XOR, then the checksum.
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.seq (WP.mono (WP.keepX (by decide) (xorPad_ok E₁ hr0 hr16 (by rw [g₁]; exact H.rbx)
      (by rw [g₁]; exact H.r12) B₁ hwn hw)) fun s₂ ⟨⟨m₂, g₂, rd₂, wr₂⟩, x₂⟩ => ?_)
    have E₂ : EnvN K W SP wn s₂ := E₁.keep (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide)) rd₂ wr₂
    have hlen₂ := hlen s₁.mem (W + BitVec.ofNat 64 112)
    have data₂ : bytesAt s₂.mem P r = Spec.Ocb.xor (bytesAt s.mem P r)
        (Spec.Ocb.toBytes (aesWith R (bytesAt s.mem K (16 * (R + 1))) (o ^^^ l))) := by
      rw [m₂, Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [hlen₂]) (by omega_arith), hlen₂,
        List.drop_of_length_le (by rw [Proof.AesCcm.X86_64.length_bytesAt]), List.append_nil, keepP₁,
        padBytes (Frame.refl _ _), xor_take_eq _ _ (by rw [Proof.AesCcm.X86_64.length_bytesAt])]
    refine WP.seq (WP.mono (WP.keepX (by decide) (padTo_ok E₂ (S := P) (n := r) (d := t2O) hr0 hr16 (by decide)
      (by rw [g₂ _ (by decide) (by decide) (by decide), g₁]; exact H.rbx)
      (by rw [g₂ _ (by decide) (by decide) (by decide), g₁]; exact H.r12)
      (by rw [rd₂, wr₂]; exact B₁.toBufN.rd) (hPT (by omega_arith)) hwn hw)) fun s₃ ⟨⟨fr₃, pad₃, g₃, rd₃, wr₃⟩, x₃⟩ => ?_)
    refine WP.mono (addPad_ok s₃ (by rw [g₃ _ (by decide) (by decide) (by decide), E₂.r15])
      (rT (by rw [rd₃, rd₂, rd₁]) (by rw [wr₃, wr₂, wr₁]))) fun s₄ ⟨x10₄, g₄, m₄, rd₄, wr₄, xo₄⟩ => ?_
    have data₄ : bytesAt s₄.mem P r = bytesAt s₂.mem P r := by
      rw [m₄, Proof.AesCcm.X86_64.bytesAt_frame fr₃ (fun q hq => by
        simp only [List.mem_singleton] at hq; subst hq; exact hPT (by omega_arith)) (by omega_arith)]
    exact {
      data := by rw [data₄, data₂]
      x12 := by rw [xo₄ _ (by decide) (by decide), x₃, x₂, x12₁]
      x10 := by
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [x10₄, rv_xor, x₃, x₂, x10₁, ← blockAtMem_eq, pad₃, data₄]
      fr := by
        rw [m₄]
        refine Frame.trans (Frame.trans (fr₁.mono (by simp)) ?_) (fr₃.mono (by simp))
        rw [m₂]
        exact (WriteBytes.writeBytes_frame (R := ⟨P, r⟩) _ _ _ (by
          rw [hlen₂]; exact Region.contains_self _ _)).mono (by simp)
      gpr := fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        rw [g₄, g₃ x hx.1 hx.2.2.1 hx.2.2.2, g₂ x hx.1 hx.2.1 hx.2.2.1, g₁]
      rd := by rw [rd₄, rd₃, rd₂, rd₁]
      wr := by rw [wr₄, wr₃, wr₂, wr₁] }
  · -- `seal`: the checksum, then the XOR.
    simp only [↓reduceIte]
    refine WP.seq (WP.mono (WP.keepX (by decide) (padTo_ok E₁ (S := P) (n := r) (d := t2O) hr0 hr16 (by decide)
      (by rw [g₁]; exact H.rbx) (by rw [g₁]; exact H.r12) B₁.toBufN.rd (hPT (by omega_arith)) hwn hw))
      fun s₂ ⟨⟨fr₂, pad₂, g₂, rd₂, wr₂⟩, x₂⟩ => ?_)
    have E₂ : EnvN K W SP wn s₂ := E₁.keep (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl <;> exact g₂ _ (by decide) (by decide) (by decide)) rd₂ wr₂
    refine WP.seq (WP.mono (addPad_ok s₂ E₂.r15 (rT (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])))
      fun s₃ ⟨x10₃, g₃, m₃, rd₃, wr₃, xo₃⟩ => ?_)
    have E₃ : EnvN K W SP wn s₃ := E₂.keep (fun x _ => by rw [g₃]) rd₃ wr₃
    refine WP.mono (WP.keepX (by decide) (xorPad_ok E₃ hr0 hr16
      (by rw [g₃, g₂ _ (by decide) (by decide) (by decide), g₁]; exact H.rbx)
      (by rw [g₃, g₂ _ (by decide) (by decide) (by decide), g₁]; exact H.r12)
      (B₁.of_eq (by rw [rd₃, rd₂]) (by rw [wr₃, wr₂])) hwn hw)) fun s₄ ⟨⟨m₄, g₄, rd₄, wr₄⟩, x₄⟩ => ?_
    have hlen₃ := hlen s₃.mem (W + BitVec.ofNat 64 112)
    exact {
      data := by
        rw [m₄, Proof.AesCcm.X86_64.bytesAt_writeBytes_base _ _ _ (by rw [hlen₃]) (by omega_arith), hlen₃,
          List.drop_of_length_le (by rw [Proof.AesCcm.X86_64.length_bytesAt]), List.append_nil, m₃, keepP fr₂,
          padBytes fr₂, xor_take_eq _ _ (by rw [Proof.AesCcm.X86_64.length_bytesAt])]
      x12 := by rw [x₄, xo₃ _ (by decide) (by decide), x₂, x12₁]
      x10 := by
        simp only [↓reduceIte]
        rw [x₄, x10₃, rv_xor, x₂, x10₁, ← blockAtMem_eq, pad₂, keepP₁]
      fr := by
        rw [m₄]
        refine Frame.trans (Frame.trans (fr₁.mono (by simp)) (fr₂.mono (by simp))) ?_
        rw [m₃]
        exact (WriteBytes.writeBytes_frame (R := ⟨P, r⟩) _ _ _ (by
          rw [hlen s₂.mem (W + 112#64)]; exact Region.contains_self _ _)).mono (by simp)
      gpr := fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        rw [g₄ x hx.1 hx.2.1 hx.2.2.1, g₃, g₂ x hx.1 hx.2.2.1 hx.2.2.2, g₁]
      rd := by rw [rd₄, rd₃, rd₂, rd₁]
      wr := by rw [wr₄, wr₃, wr₂, wr₁] }

/-! ## The tag -/

/-- `tag d`: `ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)` to `W + d`,
the checksum in `xmm10`, the offset in `xmm12`, `L_$` and `HASH` at
`W + ldO` and `W + sumO`. -/
theorem tag_ok {s : State} {K W SP : Addr} {wn R d : Nat} {ck o ld sm : Block} (E : EnvN K W SP wn s)
    (hdi : s.gpr .rdi = K) (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (h10r : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * R))
    (h10 : rv (s.xmm .xmm10) = ck) (h12 : rv (s.xmm .xmm12) = o)
    (hld : blockAtMem s.mem (W + BitVec.ofNat 64 ldO) = ld) (hsm : blockAtMem s.mem (W + BitVec.ofNat 64 sumO) = sm)
    (hd : d + 16 ≤ 640) (hd' : d = 0 ∨ d = t2O) (hwn : 640 ≤ wn) (hw : wn < 2 ^ 64) :
    WP isa (tag d) s fun s' =>
      blockAtMem s'.mem (W + BitVec.ofNat 64 d) = aesWith R (bytesAt s.mem K (16 * (R + 1))) (ck ^^^ o ^^^ ld) ^^^ sm ∧
      Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem s'.mem ∧
      (∀ x, x ∉ [Reg.rsi, .r10] → s'.gpr x = s.gpr x) ∧ s'.gpr .rsi = BitVec.ofNat 64 R ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hpx : ∀ a b : BitVec 128, XBinOp.eval .pxor a b = a ^^^ b := fun _ _ => rfl
  have hmv : ∀ a b : BitVec 128, XBinOp.eval .movdqa a b = b := fun _ _ => rfl
  have rL : InRegions (s.rd ++ s.wr) (W + 64#64) 16 := E.perm.wR (d := ldO) (n := 16) (by simp only [ldO]; omega_arith) hw
  have rS : InRegions (s.rd ++ s.wr) (W + 48#64) 16 := E.perm.wR (d := sumO) (n := 16) (by simp only [sumO]; omega_arith) hw
  unfold tag
  refine WP.seq ?_
  rw [WP.block_append_iff]
  apply WP.of_runBlock
  refine ⟨_, by orun [E.r15, rL, State.load128, XOp.exec, State.setXmm], ?_⟩
  refine WP.mono (keysR_ok _ (R := R) (by omega_arith) (by simp only [State.setXmm]; exact h10r))
    fun s₂ ⟨rsi₂, g₂, m₂, rd₂, wr₂, x₂⟩ => ?_
  simp only [State.setXmm] at g₂ m₂ rd₂ wr₂ x₂
  have keys₂ : Keys R (bytesAt s.mem K (16 * (R + 1))) s₂ := by
    have := keys_of_perm (E.perm.of_eq rd₂ wr₂) (by rw [g₂ _ (by decide), hdi]) hR
    rwa [m₂] at this
  have r10₂ : s₂.gpr .r10 = s₂.gpr .rdi + BitVec.ofNat 64 (16 * R) := by
    rw [g₂ .r10 (by decide), g₂ .rdi (by decide)]; exact h10r
  refine WP.seq (WP.mono (one_ok s₂ hR keys₂ rsi₂ r10₂) fun s₃ ⟨v₃, f₃⟩ => ?_)
  have h15₃ : s₃.gpr .r15 = W := by rw [f₃.gpr, g₂ _ (by decide), E.r15]
  have rS₃ : InRegions (s₃.rd ++ s₃.wr) (W + 48#64) 16 := by rw [f₃.rd, f₃.wr, rd₂, wr₂]; exact rS
  have wD : InRegions s₃.wr (W + BitVec.ofNat 64 d) 16 := by
    rw [f₃.wr, wr₂]; exact E.perm.wW (by omega_arith) hw
  have hx0 : rv (s₃.xmm .xmm0) = aesWith R (bytesAt s.mem K (16 * (R + 1))) (ck ^^^ o ^^^ ld) := by
    rw [v₃, x₂]
    simp only [ite_true, reduceCtorEq, ite_false, hpx, hmv]
    rw [rv_xor, rv_xor, h10, h12, ← blockAtMem_eq, show W + 64#64 = W + BitVec.ofNat 64 ldO from rfl, hld]
  have m₃ : s₃.mem = s.mem := by rw [f₃.mem, m₂]
  have post : ∀ {a : Addr}, a = W + BitVec.ofNat 64 d → InRegions s₃.wr a 16 →
      WP isa (.block [.movdquLoad .xmm11 (at_ .r15 sumO), .xop (.bin .pxor .xmm0 .xmm11),
        .movdquStore (at_ .r15 d) .xmm0]) s₃ fun s' =>
      blockAtMem s'.mem (W + BitVec.ofNat 64 d) = aesWith R (bytesAt s.mem K (16 * (R + 1))) (ck ^^^ o ^^^ ld) ^^^ sm ∧
      Frame [⟨W + BitVec.ofNat 64 d, 16⟩] s.mem s'.mem ∧
      (∀ x, x ∉ [Reg.rsi, .r10] → s'.gpr x = s.gpr x) ∧ s'.gpr .rsi = BitVec.ofNat 64 R ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := fun {a} ha wa => by
    apply WP.of_runBlock
    subst ha
    refine ⟨_, by orun [h15₃, rS₃, wa, State.load128, State.store128, XOp.exec, State.setXmm, State.setMem], ?_⟩
    refine ⟨?_, ?_, fun x hx => ?_, ?_, ?_, ?_⟩
    all_goals simp only [State.setMem, State.setXmm]
    · rw [blockAtMem_writeW]
      simp only [ite_true, hpx]
      rw [rv_xor, hx0, ← blockAtMem_eq, show W + 48#64 = W + BitVec.ofNat 64 sumO from rfl, m₃, hsm]
    · rw [← m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rw [f₃.gpr, g₂ x hx.1]
    · rw [f₃.gpr]; exact rsi₂
    · rw [f₃.rd, rd₂]
    · rw [f₃.wr, wr₂]
  exact post rfl wD

/-! ## The data -/

open VG.Proof.Ocb (ckAt dckAt encBlocks decBlocks decBlock)

theorem ckAt_xorB (p : List Byte) (m : Nat) : ckAt p m = xorB (fun i => Spec.Ocb.blockAt p i) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [ckAt, ih, xorB]

theorem dckAt_xorB (inv : Spec.Ocb.Cipher) (o0 l : Block) (c : List Byte) (m : Nat) :
    dckAt inv o0 l c m = xorB (decBlock inv o0 l c) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [dckAt, ih, xorB]

/-- The bytes of `m` blocks, from their blocks. -/
theorem bytesAt_of_blocks (mem : Mem) (D : Addr) (m : Nat) (f : Nat → Block)
    (h : ∀ i < m, blockAtMem mem (D + BitVec.ofNat 64 (16 * i)) = f i) :
    bytesAt mem D (16 * m) = (List.range m).flatMap fun i => Spec.Ocb.toBytes (f i) := by
  rw [Proof.Ocb.bytesAt_blocks, List.flatMap, List.flatMap]
  refine congrArg List.flatten (List.map_congr_left fun i hi => ?_)
  rw [← h i (List.mem_range.mp hi), blockAtMem, Proof.Ocb.toBytes_ofBytes (Proof.AesCcm.X86_64.length_bytesAt _ _ _)]

/-- What `body` needs, at its start: the data (`n` bytes at `D`), `Offset_0`
in `xmm12` and the checksum `xmm10 = 0`. -/
structure BodyPre (enc : Bool) (s : State) (K W SP D : Addr) (wn R n : Nat) (l o0 : Block) : Prop where
  env : EnvN K W SP wn s
  rdi : s.gpr .rdi = K
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  rsi : s.gpr .rsi = BitVec.ofNat 64 R
  r10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * R)
  data : s.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 lenO) 64 = BitVec.ofNat 64 n
  buf : DBufN K W SP wn s D n
  kw : (⟨K, 256⟩ : Region).Disjoint ⟨W, wn⟩
  lstar : blockAtMem s.mem (K + 240) = l
  C : ∀ t, 1 ≤ t → t ≤ 7 → blockAtMem s.mem (at' W (cSlot t)) = cAt l t
  L2 : blockAtMem s.mem (at' W l2O) = lAt l 2
  L3 : blockAtMem s.mem (at' W l3O) = lAt l 3
  x12 : rv (s.xmm .xmm12) = o0
  x10 : s.xmm .xmm10 = 0
  imc : enc = false → ImcAt R (bytesAt s.mem K (16 * (R + 1))) W s.mem
  wnLe : 640 ≤ wn
  wno : enc = false → imcO + 224 ≤ wn
  wlt : wn < 2 ^ 64

/-- What `body` writes. -/
abbrev bodyW (W D : Addr) (n : Nat) : List Region :=
  [⟨at' W ofO, 128⟩, ⟨at' W c8O, 16⟩, ⟨at' W ljO, 16⟩, ⟨at' W tmpO, 16⟩, ⟨at' W t2O, 16⟩, ⟨D, n⟩]

/-- What `body` leaves, in the terms of `encryptWith_eq` and `decryptWith_eq`:
`ciph`, `inv` the key's AES and inverse, `p` the data. -/
structure BodyPost (enc : Bool) (K W D : Addr) (R n : Nat) (l o0 : Block) (s s' : State) : Prop where
  out : bytesAt s'.mem D n =
    (if enc then encBlocks (aesWith R (bytesAt s.mem K (16 * (R + 1)))) o0 l (bytesAt s.mem D n) (n / 16)
     else decBlocks (Spec.Ocb.aesInvWith R (bytesAt s.mem K (16 * (R + 1)))) o0 l (bytesAt s.mem D n) (n / 16)) ++
    (if n % 16 > 0 then Spec.Ocb.xor (bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16))
      (Spec.Ocb.toBytes (aesWith R (bytesAt s.mem K (16 * (R + 1))) (offAt o0 l (n / 16) ^^^ l))) else [])
  x12 : rv (s'.xmm .xmm12) = if n % 16 > 0 then offAt o0 l (n / 16) ^^^ l else offAt o0 l (n / 16)
  x10 : rv (s'.xmm .xmm10) =
    (if enc then ckAt (bytesAt s.mem D n) (n / 16)
     else dckAt (Spec.Ocb.aesInvWith R (bytesAt s.mem K (16 * (R + 1)))) o0 l (bytesAt s.mem D n) (n / 16)) ^^^
    (if n % 16 > 0 then Spec.Ocb.pad (if enc then bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16)
      else Spec.Ocb.xor (bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16))
        (Spec.Ocb.toBytes (aesWith R (bytesAt s.mem K (16 * (R + 1))) (offAt o0 l (n / 16) ^^^ l)))) else 0)
  fr : Frame (bodyW W D n) s.mem s'.mem
  gpr : ∀ x, x ∉ [Reg.rax, .rdx, .rcx, .r8, .r9, .r11, .r12, .r13, .rbx, .rsi, .rbp] → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `body`. -/
theorem body_ok (enc : Bool) {s : State} {K W SP D : Addr} {wn R n : Nat} {l o0 : Block}
    (H : BodyPre enc s K W SP D wn R n l o0) :
    WP isa (body enc) s (BodyPost enc K W D R n l o0 s) := by
  have hw := H.wlt
  have hwn := H.wnLe
  have hn : n < 2 ^ 64 := H.buf.lt
  have hR14 : 16 * (R + 1) ≤ 240 := by rcases H.rounds with h | h | h <;> omega_arith
  have hmd : (if enc then Mode.seal else .open) ≠ .hash := by cases enc <;> decide
  have hmo : (if enc then Mode.seal else .open) = .open → enc = false := by cases enc <;> simp
  have rD : InRegions (s.rd ++ s.wr) (W + 208#64) 8 :=
    H.env.perm.wR (d := dataO) (n := 8) (by simp only [dataO]; omega_arith) hw
  have rL : InRegions (s.rd ++ s.wr) (W + 216#64) 8 :=
    H.env.perm.wR (d := lenO) (n := 8) (by simp only [lenO]; omega_arith) hw
  have hD : s.mem.readW (W + 208#64) 64 = D := H.data
  have hL : s.mem.readW (W + 216#64) 64 = BitVec.ofNat 64 n := H.len
  obtain ⟨s₁, run₁, r11₁, r12₁, rbp₁, g₁, m₁, rd₁, wr₁, xo₁⟩ : ∃ s₁, runBlock isa
      [ld .r11 .r15 dataO, ld .r12 .r15 lenO, Impl.AesOcb.X86_64.mvr .rbp .r12, .shift .shr .r12 4] s = some s₁ ∧
      s₁.gpr .r11 = D ∧ s₁.gpr .r12 = BitVec.ofNat 64 (n / 16) ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧
      (∀ x, x ≠ .r11 → x ≠ .r12 → x ≠ .rbp → s₁.gpr x = s.gpr x) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr ∧ s₁.xmm = s.xmm := by
    refine ⟨_, by orun [H.env.r15, rD, rL, hD, hL], ?_, ?_, ?_, fun x h1 h2 h3 => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_setFlags, ite_true, reduceCtorEq, ite_false]
    · simp only [gpr_setReg, gpr_setFlags, ite_true, reduceCtorEq, ite_false, shr4 n hn]
    · simp only [gpr_setReg, gpr_setFlags, ite_true, reduceCtorEq, ite_false]
    · simp only [gpr_setReg, gpr_setFlags, h1, h2, h3, ite_false]
    all_goals simp [mem_setReg, mem_setFlags, rd_setReg, rd_setFlags, wr_setReg, wr_setFlags, xmm_setReg,
      xmm_setFlags]
  unfold body
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have rdi₁ : s₁.gpr .rdi = K := by rw [g₁ _ (by decide) (by decide) (by decide), H.rdi]
  have P : PCtx (if enc then .seal else .open) s₁ D W wn R (bytesAt s.mem K (16 * (R + 1))) l (n / 16) := {
    nrOk := H.rounds
    keys := by
      have := keys_of_perm (H.env.perm.of_eq rd₁ wr₁) rdi₁ H.rounds
      rwa [m₁] at this
    rsi := by rw [g₁ _ (by decide) (by decide) (by decide), H.rsi]
    r10 := by rw [g₁ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide), H.r10]
    imc := fun h => by rw [m₁]; exact H.imc (hmo h)
    r15 := by rw [g₁ _ (by decide) (by decide) (by decide), H.env.r15]
    wnLe := hwn
    wno := fun h => H.wno (hmo h)
    w64 := hw
    m64 := by omega_arith
    D := by rw [rd₁, wr₁]; exact Proof.AesOcb.X86_64.covers_prefix H.buf.rd (by omega_arith)
    Dw := fun _ => by rw [wr₁]; exact Proof.AesOcb.X86_64.covers_prefix H.buf.wr (by omega_arith)
    wcov := by rw [wr₁]; exact H.env.perm.w
    DW := H.buf.w.sub_left (Region.sub_prefix (by omega_arith))
    KW := by rw [rdi₁]; exact H.kw.sub_left (Region.sub_prefix (by decide))
    KD := fun _ => by
      rw [rdi₁]; exact (H.buf.k.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by omega_arith))
    C := fun t h1 h7 => by rw [m₁]; exact H.C t h1 h7
    L2 := by rw [m₁]; exact H.L2
    L3 := by rw [m₁]; exact H.L3 }
  refine WP.seq (WP.mono (pass_ok P r12₁ r11₁ (by rw [xo₁, H.x12])) fun s₂ Q₂ => ?_)
  have hm : (if (if enc then Mode.seal else Mode.open) = .hash then ([] : List Region)
      else [⟨D, 16 * (n / 16)⟩]) = [⟨D, 16 * (n / 16)⟩] := by simp only [hmd, ↓reduceIte]
  have e1 : ofO = 512 := rfl
  have e2 : c8O = 496 := rfl
  have e3 : ljO = 336 := rfl
  have rbp₂ : s₂.gpr .rbp = BitVec.ofNat 64 n := by rw [Q₂.gpr _ (by decide), rbp₁]
  have h15₂ : s₂.gpr .r15 = W := by rw [Q₂.gpr _ (by decide), P.r15]
  obtain ⟨s₃, run₃, rbx₃, r12₃, zf₃, g₃, m₃, rd₃, wr₃, x₃⟩ : ∃ s₃, runBlock isa
      [Impl.AesOcb.X86_64.mvr .rbx .r11, Impl.AesOcb.X86_64.mvr .r12 .rbp, .alu .and .r12 (.imm 15)] s₂ = some s₃ ∧
      s₃.gpr .rbx = D + BitVec.ofNat 64 (16 * (n / 16)) ∧ s₃.gpr .r12 = BitVec.ofNat 64 (n % 16) ∧
      s₃.zf = some (decide (n % 16 = 0)) ∧ (∀ x, x ≠ .rbx → x ≠ .r12 → s₃.gpr x = s₂.gpr x) ∧ s₃.mem = s₂.mem ∧
      s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr ∧ s₃.xmm = s₂.xmm := by
    have e15 : BitVec.signExtend 64 (15 : BitVec 32) = 15#64 := by decide
    have ea : BitVec.ofNat 64 n &&& 15#64 = BitVec.ofNat 64 (n % 16) := by
      rw [and15', BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
    refine ⟨_, by orun [], ?_, ?_, ?_, fun x h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, reduceCtorEq, ite_false, Q₂.r11]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, ite_true, reduceCtorEq, ite_false, e15, rbp₂, ea]
    · simp only [zf_setReg, zf_arithFlags, zf_setFlags, gpr_setReg, gpr_arithFlags, ite_true, reduceCtorEq,
        ite_false, e15, rbp₂, ea]
      by_cases h : n % 16 = 0
      · simp [h]
      · have : BitVec.ofNat 64 (n % 16) ≠ 0#64 := fun h' => h (by
          have := congrArg BitVec.toNat h'
          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)] at this)
        simp [h, this]
    · simp only [gpr_setReg, gpr_arithFlags, gpr_setFlags, h1, h2, ite_false]
    all_goals simp only [mem_setReg, mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg,
      wr_arithFlags, wr_setFlags, xmm_setReg, xmm_arithFlags, xmm_setFlags]
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  -- What the pass leaves of `s`.
  have keep₂ : ∀ {p : Addr} {k : Nat}, (⟨p, k⟩ : Region).Disjoint ⟨W, wn⟩ →
      (⟨p, k⟩ : Region).Disjoint ⟨D, 16 * (n / 16)⟩ → k ≤ 2 ^ 64 → bytesAt s₂.mem p k = bytesAt s.mem p k :=
    fun {p k} hW hDm hk => by
      rw [Proof.AesCcm.X86_64.bytesAt_frame Q₂.fr (fun r hr => by
        simp only [passW, hm, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with (rfl | rfl | rfl) | rfl
        · exact hW.sub_right (Offset.sub_base W (by omega_arith))
        · exact hW.sub_right (Offset.sub_base W (by omega_arith))
        · exact hW.sub_right (Offset.sub_base W (by omega_arith))
        · exact hDm) hk, m₁]
  have sched₂ : bytesAt s₂.mem K (16 * (R + 1)) = bytesAt s.mem K (16 * (R + 1)) :=
    keep₂ (H.kw.sub_left (Region.sub_prefix (by omega_arith)))
      ((H.buf.k.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Region.sub_prefix (by omega_arith)))
      (by omega_arith)
  have lstar₂ : blockAtMem s₂.mem (K + 240) = l := by
    rw [blockAtMem, show (K + 240 : Addr) = K + BitVec.ofNat 64 240 from rfl,
      keep₂ (H.kw.sub_left (Offset.sub_base K (by decide)))
        ((H.buf.k.sub_left (Offset.sub_base K (by decide))).sub_right (Region.sub_prefix (by omega_arith)))
        (by decide)]
    exact H.lstar
  have tail₂ : bytesAt s₂.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) =
      bytesAt s.mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) :=
    keep₂ (H.buf.w.sub_left (Offset.sub_base D (by omega_arith))) (Offset.disjoint_base D (Nat.le_refl _)
      (by omega_arith)) (by omega_arith)
  have hsplit : ∀ mem : Mem, bytesAt mem D n =
      bytesAt mem D (16 * (n / 16)) ++ bytesAt mem (D + BitVec.ofNat 64 (16 * (n / 16))) (n % 16) := fun mem => by
    have := Proof.Ocb.bytesAt_append mem D (16 * (n / 16)) (n % 16)
    rwa [Nat.div_add_mod] at this
  have blk : ∀ i < n / 16, blockAtMem s₁.mem (at' D (16 * i)) = Spec.Ocb.blockAt (bytesAt s.mem D n) i :=
    fun i hi => by rw [m₁, Proof.Ocb.blockAt_bytesAt _ _ (by omega_arith)]
  have hX : rv (s₃.xmm .xmm10) = if enc then ckAt (bytesAt s.mem D n) (n / 16)
      else dckAt (Spec.Ocb.aesInvWith R (bytesAt s.mem K (16 * (R + 1)))) o0 l (bytesAt s.mem D n) (n / 16) := by
    rw [x₃, Q₂.x10, xo₁, H.x10, rv_zero, show ∀ x : Block, (0 : Block) ^^^ x = x from fun x => by simp]
    cases enc
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [dckAt_xorB]
      refine xorB_congr fun i hi => ?_
      simp only [termB, term, ↓reduceIte, bF_open, Proof.Ocb.decBlock]
      rw [blk i hi]
    · simp only [↓reduceIte]
      rw [ckAt_xorB]
      refine xorB_congr fun i hi => ?_
      simp only [termB, term]
      rw [blk i hi]
  have hO : rv (s₃.xmm .xmm12) = offAt o0 l (n / 16) := by rw [x₃, Q₂.x12]
  have hOut : bytesAt s₂.mem D (16 * (n / 16)) =
      if enc then encBlocks (aesWith R (bytesAt s.mem K (16 * (R + 1)))) o0 l (bytesAt s.mem D n) (n / 16)
      else decBlocks (Spec.Ocb.aesInvWith R (bytesAt s.mem K (16 * (R + 1)))) o0 l (bytesAt s.mem D n) (n / 16) := by
    rw [bytesAt_of_blocks s₂.mem D (n / 16) _ (fun i hi => Q₂.out hmd i hi)]
    cases enc
    · simp only [Bool.false_eq_true, ↓reduceIte, decBlocks, List.flatMap]
      refine congrArg List.flatten (List.map_congr_left fun i hi => ?_)
      simp only [outB, ↓reduceIte, bF_open, Proof.Ocb.decBlock]
      rw [blk i (List.mem_range.mp hi)]
    · simp only [↓reduceIte, encBlocks, List.flatMap]
      refine congrArg List.flatten (List.map_congr_left fun i hi => ?_)
      simp only [outB, bF_seal]
      rw [blk i (List.mem_range.mp hi)]
  have hsub : ∀ r ∈ passW (if enc then .seal else .open) W D (n / 16), ∃ r' ∈ bodyW W D n, Region.Sub r r' :=
    fun r hr => by
      simp only [passW, hm, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl) | rfl
      · exact ⟨_, by simp [bodyW], fun _ h => h⟩
      · exact ⟨_, by simp [bodyW], fun _ h => h⟩
      · exact ⟨_, by simp [bodyW], fun _ h => h⟩
      · exact ⟨⟨D, n⟩, by simp [bodyW], Region.sub_prefix (by omega_arith)⟩
  have fr₃ : Frame (bodyW W D n) s.mem s₃.mem := by rw [m₃, ← m₁]; exact Q₂.fr.sub hsub
  have g₃' : ∀ x, x ∉ [Reg.rax, .rdx, .rcx, .r8, .r9, .r11, .r12, .r13, .rbx, .rsi, .rbp] → s₃.gpr x = s.gpr x :=
    fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rw [g₃ x hx.2.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.1, Q₂.gpr x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1,
        hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.1]),
        g₁ x (fun h => hx.2.2.2.2.2.1 h) (fun h => hx.2.2.2.2.2.2.1 h) (fun h => hx.2.2.2.2.2.2.2.2.2.2 h)]
  by_cases hr : n % 16 = 0
  · refine WP.ite true (by simp [isa, eval, zf₃, hr]) (fun _ => WP.block_nil ?_) (fun h => absurd h (by decide))
    have hb0 : ∀ (mem : Mem) (p : Addr), bytesAt mem p 0 = [] := fun _ _ => rfl
    exact {
      out := by
        rw [hsplit s₃.mem, m₃, hOut, hr, hb0]
        simp only [gt_iff_lt, Nat.lt_irrefl, ↓reduceIte]
      x12 := by simp only [hr, gt_iff_lt, Nat.lt_irrefl, ↓reduceIte]; exact hO
      x10 := by simp only [hr, gt_iff_lt, Nat.lt_irrefl, ↓reduceIte]; rw [hX]; exact BitVec.xor_zero.symm
      fr := fr₃
      gpr := g₃'
      rd := by rw [rd₃, Q₂.rd, rd₁]
      wr := by rw [wr₃, Q₂.wr, wr₁] }
  · refine WP.ite false (by simp [isa, eval, zf₃, hr]) (fun h => absurd h (by decide)) fun _ => ?_
    have hrp : n % 16 > 0 := by omega_arith
    have E₃ : EnvN K W SP wn s₃ := H.env.keep (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl
        all_goals exact g₃' _ (by decide))
      (by rw [rd₃, Q₂.rd, rd₁]) (by rw [wr₃, Q₂.wr, wr₁])
    have R₃ : RestPre s₃ K W SP (D + BitVec.ofNat 64 (16 * (n / 16))) wn R (n % 16) l (offAt o0 l (n / 16))
        (rv (s₃.xmm .xmm10)) := {
      env := E₃
      rdi := by rw [g₃' _ (by decide), H.rdi]
      rounds := H.rounds
      rsi := by rw [g₃ _ (by decide) (by decide), Q₂.gpr _ (by decide), P.rsi]
      r10 := by
        rw [g₃ _ (by decide) (by decide), Q₂.gpr _ (by decide), g₃ _ (by decide) (by decide), Q₂.gpr _ (by decide),
          P.r10]
      rbx := rbx₃
      r12 := r12₃
      r0 := hrp
      r16 := Nat.mod_lt _ (by decide)
      buf := (H.buf.slice (a := 16 * (n / 16)) (k := n % 16) (by omega_arith)).of_eq
        (by rw [rd₃, Q₂.rd, rd₁]) (by rw [wr₃, Q₂.wr, wr₁])
      lstar := by rw [m₃]; exact lstar₂
      x12 := hO
      x10 := rfl
      wnLe := hwn
      wlt := hw }
    refine WP.mono (rest_ok enc R₃) fun s₄ Q₄ => ?_
    have e112 : tmpO = 112 := rfl
    have e128 : t2O = 128 := rfl
    have head₄ : bytesAt s₄.mem D (16 * (n / 16)) = bytesAt s₂.mem D (16 * (n / 16)) := by
      rw [Proof.AesCcm.X86_64.bytesAt_frame Q₄.fr (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (H.buf.w.sub_left (Region.sub_prefix (by omega_arith))).sub_right (LayN.wSub (by omega_arith))
        · exact (H.buf.w.sub_left (Region.sub_prefix (by omega_arith))).sub_right (LayN.wSub (by omega_arith))
        · exact Offset.base_disjoint D (Nat.le_refl _) (by omega_arith)) (by omega_arith), m₃]
    exact {
      out := by
        rw [hsplit s₄.mem, head₄, hOut, Q₄.data, m₃, tail₂, sched₂]
        simp only [hrp, ↓reduceIte]
      x12 := by rw [Q₄.x12]; simp only [hrp, ↓reduceIte]
      x10 := by
        rw [Q₄.x10, hX]
        simp only [hrp, ↓reduceIte]
        cases enc
        · simp only [Bool.false_eq_true, ↓reduceIte]; rw [Q₄.data, m₃, tail₂, sched₂]
        · simp only [↓reduceIte]; rw [m₃, tail₂]
      fr := by
        refine fr₃.trans (Q₄.fr.sub fun r hr => ?_)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨_, by simp [bodyW], fun _ h => h⟩
        · exact ⟨_, by simp [bodyW], fun _ h => h⟩
        · exact ⟨⟨D, n⟩, by simp [bodyW], Offset.sub_base D (by omega_arith)⟩
      gpr := fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        rw [Q₄.gpr x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.2.2.2.2.2.2.1]), g₃' x (by simp [hx.1, hx.2.1,
          hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.2.1,
          hx.2.2.2.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.2.2.2])]
      rd := by rw [Q₄.rd, rd₃, Q₂.rd, rd₁]
      wr := by rw [Q₄.wr, wr₃, Q₂.wr, wr₁] }

end VG.Proof.AesOcb.X86_64.AesNi
