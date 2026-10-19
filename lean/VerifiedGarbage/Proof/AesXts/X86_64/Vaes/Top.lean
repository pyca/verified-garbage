module

public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Setup
public import VerifiedGarbage.Proof.AesXts.Spec
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Tail
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Body
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey

/-!
# One-pass XTS-AES on x86-64: the whole function

`crypt_wp`: `crypt pre L f` meets the contract of `vg_aes_xts_encrypt` (or
`vg_aes_xts_decrypt`), given that `pre` sets up what the rounds need (`KP`)
without disturbing the tweaks, that the loop `L` takes groups of eight blocks
(`LoopOk`; `loop8_ok` for `loop8`), and that `f` computes the cipher (or its
inverse) on `xmm0`.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc (ciphOf)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0 modeX86_64)
open VG.Impl.AesXts.X86_64Vaes (bufOff finish)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (ea_at ofInt_natCast)

theorem getElem_tweaks (t : List Byte) {n k : Nat} (hk : k < n) :
    (Spec.Xts.tweaks t n)[k]'(by rw [AesXts.length_tweaks]; exact hk) = Spec.Xts.next t k := by
  induction n generalizing t k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k => simp only [Spec.Xts.tweaks, List.getElem_cons_succ]; rw [ih _ (by omega), AesXts.next_succ']

/-- After the setup, with what the rounds need. -/
theorem SInvK.ginv {enc : Bool} {KP : State → Prop} {s₀ : State} (hp : UPre s₀) {s : State} (hk : SInvK s₀ s)
    (hkp : KP s) : GInv enc KP s₀ 0 0 s :=
  have h := hk.1
  { kp := hkp
    le := Nat.zero_le _
    r8 := h.r8
    r9 := by rw [h.r9, Nat.sub_zero]
    r11 := by rw [h.r11, blk, Nat.mul_zero]; exact (BitVec.add_zero _).symm
    r10 := hk.2
    keep := h.keep
    rd := h.rd
    wr := h.wr
    frame := h.frame.mono fun r hr => by simp at hr; simp [hr]
    data := fun k hk => by
      simp only [Nat.not_lt_zero, ite_false]
      exact AesCbc.X86_64.bytesAt_frame h.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.data_scr.sub_left (UPre.data_sub hk)) (by decide)
    buf := fun j hj => by rw [h.buf j hj, Nat.zero_add]
    rdx := h.rdx }

/-- The contract, from `GInv … N` and the tweak after the last block stored. -/
theorem post_of {enc : Bool} {KP : State → Prop} {s₀ : State} (hp : UPre s₀) {b : Nat} {s : State}
    (h : GInv enc KP s₀ b (N s₀) s) (s' : State) (hf : Frame [ivR s₀] s.mem s'.mem)
    (hiv : bytesAt s'.mem (Iv s₀) 16 = Spec.Xts.next (iv0 s₀) (N s₀))
    (hgs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) :
    gprPreserved s₀ s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s₀ s' := by
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_⟩
  · rw [hgs r hr]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [hf.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.ret_iv) (by decide),
      h.frame.readW (r := ⟨s₀.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.ret_data
        · exact hp.ret_scr) (by decide)]
  · show Spec.Cbc.blocksAt s'.mem (Dp s₀) (N s₀) = Spec.Xts.crypt (ciphOf enc (R s₀) (wK s₀)) (iv0 s₀)
      (Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀))
    apply List.ext_getElem (by rw [AesXts.length_crypt, AesCbc.length_blocksAt, AesCbc.length_blocksAt])
    intro k h₁ h₂
    have hk : k < N s₀ := by rwa [AesCbc.length_blocksAt] at h₁
    rw [AesCbc.getElem_blocksAt _ _ hk]
    simp only [Spec.Xts.crypt, List.getElem_zipWith]
    rw [getElem_tweaks _ (by rwa [AesCbc.length_blocksAt]), AesCbc.getElem_blocksAt _ _ hk,
      AesCbc.X86_64.bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.iv_data.sub_right (UPre.data_sub hk)).symm)
        (by decide), h.data k hk]
    simp only [hk, ite_true]
  · show bytesAt s'.mem (Iv s₀) 16 = Spec.Xts.next (iv0 s₀) (Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀)).length
    rw [AesCbc.length_blocksAt, hiv]

/-- The tweak after the last block copied to the tweak pointer. -/
theorem finish_wp {enc : Bool} {KP : State → Prop} {s₀ : State} (hp : UPre s₀) {b : Nat} {s : State}
    (h : TInv enc KP s₀ b (N s₀) s) :
    WP isa (.block finish) s fun s' => gprPreserved s₀ s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s₀ s' := by
  have hg := h.g
  have hsw := hp.scr_wrap
  have hlt := h.lt
  have hbc := h.bc
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [hg.wr, hp.wr]
  have hR : s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by rw [hg.rd, hW, hp.rd]; rfl
  have z0 : BitVec.ofInt 64 ((0 : Nat) : Int) = 0#64 := rfl
  have z8 : BitVec.ofInt 64 ((8 : Nat) : Int) = BitVec.ofNat 64 8 := rfl
  let T := slot s₀ (N s₀ - b)
  have inT0 : InRegions (s.rd ++ s.wr) (s.gpr .rax + 0#64) 8 := ⟨scrR s₀, by rw [hR]; simp, by
    rw [h.rax]; simpa using Offset.contains_base (S s₀) (d := bufOff + 16 * (N s₀ - b)) (n := 8) (k := 2176)
      (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩
  have inI0 : InRegions s.wr (Iv s₀ + 0#64) 8 := ⟨ivR s₀, by rw [hW]; simp, by simpa using AesCbc.X86_64.cIv0⟩
  have inI8 : InRegions s.wr (Iv s₀ + BitVec.ofNat 64 8) 8 := ⟨ivR s₀, by rw [hW]; simp, AesCbc.X86_64.cIv8⟩
  have inT8 : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 8) 8 := ⟨scrR s₀, by rw [hR]; simp, by
    rw [h.rax, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩
  have hrdx := hg.rdx
  apply WP.of_runBlock
  simp only [finish, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.setReg, State.load64, State.store64, ea_at, z0, z8, hrdx, inT0, inT8, inI0, inI8,
    Option.map_some, Option.some.injEq, exists_eq_left']
  simp only [BitVec.add_zero]
  have hT8 : Region.Disjoint ⟨T + BitVec.ofNat 64 8, 8⟩ ⟨Iv s₀, 8⟩ := by
    have hiv : Region.Disjoint (scrR s₀) ⟨Iv s₀, 8⟩ :=
      hp.iv_scr.symm.sub_right (Region.sub_prefix (len := 8) (len' := 16) (by decide))
    refine hiv.sub_left ?_
    show Region.Sub ⟨slot s₀ (N s₀ - b) + BitVec.ofNat 64 8, 8⟩ (scrR s₀)
    rw [slot, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.sub_base _ (by simp only [bufOff]; omega)
  have f1 : Frame [⟨Iv s₀, 8⟩] s.mem (s.mem.writeW (Iv s₀) (s.mem.readW T 64)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [h.rax]
  refine post_of hp hg _ (AesCbc.frame_store2 _ _ _) ?_ fun r hr => ?_
  · rw [Proof.Cmac.bytesAt_store2, f1.readW (r := ⟨T + BitVec.ofNat 64 8, 8⟩) (Region.contains_self _ _)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hT8) (by decide)]
    rw [← tw, tw_readW, hg.buf _ (by omega), show b + (N s₀ - b) = N s₀ by omega]
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

open VG.Impl.AesXts.X86_64Vaes (crypt enter gen loop8)

/-- `L` takes groups of eight blocks while eight are left: from `GInv 0 0`,
with `cmp r9, 8` done, to `GInv c c` with fewer than eight left. -/
def LoopOk (enc : Bool) (L : Prog isa) (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s, GInv enc KP s₀ 0 0 s → s.cf = some (decide (N s₀ < 8)) →
    WP isa L s fun s' => ∃ c, N s₀ - c < 8 ∧ GInv enc KP s₀ c c s'

theorem loop8_ok {enc : Bool} {KP : State → Prop} {f8 : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf8 : Blk8 enc f8 KP s₀) : LoopOk enc (loop8 f8) KP s₀ :=
  fun _ h hcf => groups_wp hp hst hf8 h hcf

/-- The function's body, with at least one block. -/
theorem body_wp {enc : Bool} {KP : State → Prop} {pre L : Prog isa} {f : List XReg → Prog isa} {s₀ : State}
    (hp : UPre s₀) (hst : Stable KP s₀) (hL : LoopOk enc L KP s₀) (hf : Blk1 enc f KP s₀)
    (hpre : ∀ s, SInvK s₀ s → WP isa pre s fun s' => SInvK s₀ s' ∧ KP s') :
    WP isa (.seq (.block (enter ++ gen)) (.seq pre (.seq (.block [.alu .cmp .r9 (.imm 8)])
      (.seq L (.seq (Impl.AesXts.X86_64Vaes.tail f) (.block finish)))))) s₀
      fun s' => gprPreserved s₀ s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s₀ s' := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (enter_ok hp) fun s₁ h₁ => WP.mono (gen_all_ok hp h₁) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (hpre s₂ h₂) fun s₃ ⟨h₃, kp₃⟩ => ?_)
  have g₃ := SInvK.ginv (enc := enc) hp h₃ kp₃
  refine WP.seq (WP.mono (cmp8_ok hst g₃) fun s₄ ⟨g₄, cf₄⟩ => ?_)
  refine WP.seq (WP.mono (hL s₄ g₄ (by simpa using cf₄)) fun s₅ ⟨c, hc, g₅⟩ => ?_)
  exact WP.seq (WP.mono (tail_wp hp hst hf (by omega) g₅) fun s₆ h₆ => finish_wp hp h₆)

/-- The whole function. -/
theorem crypt_wp {enc : Bool} {KP : State → State → Prop} {pre L : Prog isa} {f : List XReg → Prog isa} {s₀ : State}
    (h0 : (modeX86_64 (AesXts.xtsMode enc)).pre s₀)
    (hst : ∀ s₁ : State, UPre s₁ → Stable (KP s₁) s₁)
    (hL : ∀ s₁ : State, UPre s₁ → LoopOk enc L (KP s₁) s₁)
    (hf : ∀ s₁ : State, UPre s₁ → Blk1 enc f (KP s₁) s₁)
    (hpre : ∀ s₁ : State, UPre s₁ → ∀ s, SInvK s₁ s → WP isa pre s fun s' => SInvK s₁ s' ∧ KP s₁ s') :
    WP isa (crypt pre L f) s₀ fun s' => gprPreserved s₀ s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s₀ s' := by
  have hn : N s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  have st : WP isa (.block [.alu .test .r8 (.reg .r8)]) s₀ fun s₁ =>
      s₁.gpr = s₀.gpr ∧ s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧ s₁.zf = some (decide (N s₀ = 0)) := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some,
      Option.some.injEq, exists_eq_left']
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    simp only [arithFlags, State.setFlags, BitVec.and_self]
    have e : s₀.gpr .r8 = BitVec.ofNat 64 (N s₀) := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [e, Aes.X86_64.AesNi.Ecb.beq_ofNat_zero' hn]
  refine WP.seq (WP.mono st fun s₁ ⟨g, m, rd, wr, zf⟩ => ?_)
  refine WP.ite (decide (N s₀ = 0)) (by simp [eval, zf]) (fun hz => ?_) (fun hz => ?_)
  · simp at hz
    refine WP.block_nil ⟨⟨fun r _ => by rw [g], by rw [m]⟩, ?_, ?_⟩
    · show Spec.Cbc.blocksAt s₁.mem (Dp s₀) (N s₀) = Spec.Xts.crypt _ _ (Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀))
      rw [hz]; rfl
    · show bytesAt s₁.mem (Iv s₀) 16 = Spec.Xts.next _ (Spec.Cbc.blocksAt s₀.mem (Dp s₀) (N s₀)).length
      rw [AesCbc.length_blocksAt, hz, m]; rfl
  · have h1 : (modeX86_64 (AesXts.xtsMode enc)).pre s₁ := by
      simp only [modeX86_64, g, rd, wr]; simpa only [modeX86_64] using h0
    have hp₁ := UPre.of h1
    refine WP.mono (body_wp hp₁ (hst s₁ hp₁) (hL s₁ hp₁) (hf s₁ hp₁) (hpre s₁ hp₁)) fun s' ⟨gp, po⟩ => ?_
    refine ⟨⟨fun r hr => by rw [gp.1 r hr, g], by rw [← m, ← g]; exact gp.2⟩, ?_⟩
    simp only [modeX86_64, g, m] at po ⊢
    exact po

end VG.Proof.AesXts.X86_64.Vaes
