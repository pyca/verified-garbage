module

public import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Run
public import VerifiedGarbage.Proof.AesXts.Unit
public import VerifiedGarbage.Proof.AesXts.X86_64.Variant
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Steps
import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Pre
import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
import VerifiedGarbage.Proof.Framework.Offset

/-!
# XTS-AES of data units on x86-64: encryption

`encrypt_wp`: the tweak, the call on the whole blocks, and for a partial
block the swap and the call on the last whole block, then the epilogue,
for any implementation `v` of the whole-block functions (`XtsImpl`). The
data unit is `encWith` of the cipher and the tweak, which is
`aesXtsEncrypt` of any key whose schedules are given (`unit_post`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Unit

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesXts.X86_64Unit
open VG.Proof.AesCbc.X86_64 (modeX86_64 in_rw)
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

/-- The data unit's result in a direction. -/
def withOf : Bool → Spec.Cbc.Cipher → List Byte → List Byte → List Byte
  | true => encWith
  | false => decWith

/-- What each branch leaves before the epilogue. -/
structure Fin (enc : Bool) (s₀ s : State) : Prop where
  inv : Inv s₀ s
  data : bytesAt s.mem (D s₀) (Len s₀) =
    withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (D s₀) (Len s₀))

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem AllPost.keep {enc : Bool} {N : Nat} {s s' : State} (h : AllPost enc s₀ N s)
    (hg : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r15, .rsp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : AllPost enc s₀ N s' where
  inv := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _) hg hrd hwr
  out := by rw [hm]; exact h.out
  tw := by rw [hm]; exact h.tw
  frame := by rw [hm]; exact h.frame

/-- The steal's prologue: the last whole block in `rdx`, and the index in `rcx`. -/
theorem stealPre_wp {s : State} (hr12 : s.gpr .r12 = D s₀) (hrax : s.gpr .rax = BitVec.ofNat 64 (16 * M s₀))
    {Q : State → Prop}
    (h : ∀ s', s'.gpr .rdx = L s₀ → s'.gpr .rcx = 0 → (∀ r, r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block stealPre) s Q := by
  rw [stealPre, WP.block_append_iff]
  obtain ⟨s₁, run₁, rdx₁, g₁, mem₁, rd₁, wr₁⟩ := lastAddr_ok s
  refine WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₁.setReg .rcx (BitVec.setWidth 64 (0 : BitVec 32)), by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some, State.setReg32], ?_⟩⟩
  refine h _ ?_ (by simp [gpr_setReg]) (fun r h₁ h₂ => ?_) (by rw [mem_setReg, mem₁]) (by rw [rd_setReg, rd₁])
    (by rw [wr_setReg, wr₁])
  · rw [gpr_setReg_of_ne _ _ (by decide), rdx₁, hr12, hrax, last_eq _ hp.m_pos (by have := hp.m_lt; omega)]
  · rw [gpr_setReg_of_ne _ _ h₂, g₁ r h₁]

/-- After `split`, following the call on the whole blocks. -/
structure SplitPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  all : AllPost enc s₀ N s
  rax : s.gpr .rax = BitVec.ofNat 64 (16 * M s₀)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (B s₀)
  zf : s.zf = some (decide (B s₀ = 0))

/-- Before the call on the last whole block, from the tweak of block `M`:
`Cₘ` and `PP` swapped into place. -/
structure EncLast (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (Tp s₀) (L s₀) (S s₀) 1 (R s₀)
  mem : ∃ m, AllMem true s₀ (M s₀) m ∧ s.mem = swapMem m (L s₀) (B s₀)

theorem encLast_wp {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block stealPre) swap) (.block (argsL tO))) s (EncLast s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  refine WP.seq (WP.seq (stealPre_wp hp (by rw [h.all.inv.r12]) h.rax fun s₁ rdx₁ rcx₁ g₁ mem₁ rd₁ wr₁ => ?_))
  have wr₁' : s₁.wr = [dataR s₀, scrR s₀] := by rw [wr₁, h.all.inv.wr, hp.wr]
  refine WP.mono (swap_ok s₁ (Nat.pos_of_ne_zero hB) hb rdx₁ rcx₁
    (by rw [g₁ _ (by decide) (by decide), h.r8]) (fun i hi => by
      rw [wr₁']
      exact in_rw (r := dataR s₀) (by simp)
        (hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega) (by omega)))))
    fun s₂ ⟨mem₂, g₂, rd₂, wr₂⟩ => ?_
  obtain ⟨s₃, run₃, rdi₃, rsi₃, rdx₃, rcx₃, r8₃, r9₃, cs₃, mem₃, rd₃, wr₃⟩ := argsL_ok s₂ (o := tO) rfl
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have k₂ (r : Reg) (hr : r ∈ pinned) : s₂.gpr r = s.gpr r := by
    have n := pinned_ne hr
    rw [g₂ r n.1 n.2.2.2.2 n.2.1, g₁ r n.2.2.1 n.2.1]
  have k₃ (r : Reg) (hr : r ∈ pinned) : s₃.gpr r = s.gpr r := by
    rw [cs₃ r (pinned_cs r hr), k₂ r hr]
  have inv₂ : Inv s₀ s₂ := Inv.step hp h.all.inv (rs := [⟨L s₀, 16 + B s₀⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl hp.lb_sub)
    (by rw [mem₂, mem₁]; exact Proof.AesXts.Unit.swapMem_frame _ _ _) k₂ (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have inv₃ : Inv s₀ s₃ := Inv.step hp inv₂ (rs := []) (fun _ h => by simp at h)
    (by rw [mem₃]; exact Frame.refl _ _) (fun r hr => by rw [k₃ r hr, k₂ r hr]) rd₃ wr₃
  exact ⟨inv₃, xpre_last hp inv₃.rd inv₃.wr inv₃.rsp (.inl rfl) (by rw [rdi₃, inv₂.rbx])
    (by rw [rsi₃, inv₂.rbp, rsi_ofNat]) (by rw [rdx₃, inv₂.r15]) (by rw [rcx₃, g₂ _ (by decide) (by decide)
      (by decide), rdx₁]) r8₃ (by rw [r9₃, inv₂.r15]),
    ⟨s.mem, h.all.mem, by rw [mem₃, mem₂, mem₁]⟩⟩

/-- The call on the last whole block, and the data unit's ciphertext. -/
theorem encLastCall_wp (v : XtsImpl) {s : State} (h : EncLast s₀ s) (hB : B s₀ ≠ 0) :
    WP isa (.call v.enc.name v.enc.code) s (Fin true s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨m, ⟨hout, htw, hfr⟩, m₂⟩ := h.mem
  refine WP.mono (xts_call true v.encOk v.encNosp v.encDepth h.pre) fun s₄ c => ?_
  have sw := Proof.AesXts.Unit.swapMem_frame m (L s₀) (B s₀)
  refine ⟨Inv.call hp h.inv t_sub (.inl hp.l_sub) c, ?_⟩
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.enc_steal hp.m_pos (Nat.pos_of_ne_zero hB) hb hout ?_ ⟨?_, ?_, ?_⟩
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.tl_blocks
      · exact hp.data_scr.sub_left hp.tl_sub
      · exact hp.stk_data.symm.sub_left hp.tl_sub) (by omega)
  · rw [Proof.AesXts.Unit.crypt_one_of c.out,
      hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp), m₂,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left (sub_trans t_sub s_sub)).sub_right hp.lb_sub) (by decide), htw]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega)) hp.hd_l
      (sub_trans t_sub s_sub) h.inv.rsp c (by dsimp only; have := hp.wrapD; omega), m₂]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l (sub_trans t_sub s_sub) h.inv.rsp c
      (by dsimp only; omega), m₂]

/-- The steal of encryption: `Cₘ` and `PP` swapped into place, and `PP`
enciphered with the tweak of block `M`. -/
theorem encSteal_wp (v : XtsImpl) {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (encSteal v.enc) s (Fin true s₀) :=
  WP.assoc (WP.assoc (WP.seq (WP.mono (encLast_wp hp h hB) fun _ h' => encLastCall_wp hp v h' hB)))

/-- The postcondition, from the bytes of the data unit. -/
theorem unit_post {enc : Bool} {s' : State}
    (hd : bytesAt s'.mem (D s₀) (Len s₀) = withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (D s₀) (Len s₀))) :
    (unitX86_64 enc).post s₀ s' := by
  intro key hk
  have hk' := Proof.AesXts.Unit.keys_of (bytesAt s₀.mem (I s₀) 16) hk
  have hl : 16 ≤ (bytesAt s₀.mem (D s₀) (Len s₀)).length := by
    rw [Proof.AesXts.Unit.length_bytesAt]; exact hp.len_lo
  cases enc
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsDecrypt_eq hk' hl, hd]; rfl
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsEncrypt_eq hk' hl, hd]; rfl

omit hp in
/-- After `split`: the bytes of the whole blocks in `rax`, the bytes after
them in `r8`, and ZF set if there are none. -/
theorem split_wp {s : State} (h : Inv s₀ s) {Q : State → Prop}
    (hq : ∀ s', s'.gpr .rax = BitVec.ofNat 64 (16 * M s₀) → s'.gpr .r8 = BitVec.ofNat 64 (B s₀) →
      s'.zf = some (decide (B s₀ = 0)) → (∀ r, r ≠ .rax → r ≠ .r8 → s'.gpr r = s.gpr r) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block split) s Q := by
  obtain ⟨s', run', rax', r8', zf', g', mem', rd', wr'⟩ := split_ok s
  rw [h.r13] at rax' r8' zf'
  exact WP.of_runBlock ⟨s', run', hq s' rax' r8' zf' g' mem' rd' wr'⟩

/-- The arguments of the call on the whole blocks. -/
theorem argsAll_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsAll) s (BlocksReady s₀ (M s₀)) := by
  obtain ⟨s₂, run₂, rdi₂, rsi₂, rdx₂, rcx₂, r8₂, r9₂, cs₂, mem₂, rd₂, wr₂⟩ := argsAll_ok s
  have h₂ := TwPost.keep hp h cs₂ mem₂ rd₂ wr₂
  exact WP.of_runBlock ⟨s₂, run₂, h₂, xpre_blocks hp h₂.inv.rd h₂.inv.wr h₂.inv.rsp (N := M s₀)
    (by rw [len_eq s₀]; omega) (by rw [rdi₂, h.inv.rbx]) (by rw [rsi₂, h.inv.rbp, rsi_ofNat])
    (by rw [rdx₂, h.inv.r15]) (by rw [rcx₂, h.inv.r12]) (by rw [r8₂, h.inv.r13]) (by rw [r9₂, h.inv.r15])⟩

theorem splitAll_wp {enc : Bool} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    WP isa (.block split) s (SplitPost enc s₀ N) :=
  split_wp h.inv fun _ rax₄ r8₄ zf₄ g₄ mem₄ rd₄ wr₄ =>
    ⟨AllPost.keep hp h (fun r hr => g₄ r (pinned_ne hr).1 (pinned_ne hr).2.2.2.1) mem₄ rd₄ wr₄, rax₄, r8₄, zf₄⟩

omit hp in
/-- The data unit of whole blocks, after the call on all of them. -/
theorem whole_fin {enc : Bool} {s : State} (h : AllPost enc s₀ (M s₀) s) (hb : B s₀ = 0) : Fin enc s₀ s := by
  refine ⟨h.inv, ?_⟩
  rw [show Len s₀ = 16 * M s₀ by rw [len_eq s₀, hb, Nat.add_zero]]
  cases enc
  · exact Proof.AesXts.Unit.dec_whole h.out
  · exact Proof.AesXts.Unit.enc_whole h.out

theorem encrypt_wp (v : XtsImpl) :
    WP isa (Impl.AesXts.X86_64Unit.encrypt v.xts) s₀ fun s' => gprPreserved s₀ s' ∧ (unitX86_64 true).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp v.encOk v.encNosp v.encDepth) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (argsAll_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (blocks_call hp true v.encOk v.encNosp v.encDepth (by rw [len_eq s₀]; omega) h₂.tw
    h₂.pre) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (splitAll_wp hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) h₄.zf (fun hb => WP.block_nil (whole_fin h₄.all (by simpa using hb)))
    (fun hb => encSteal_wp hp v h₄ (by simpa using hb))) fun s₅ h₅ => ?_)
  exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.X86_64.Unit
