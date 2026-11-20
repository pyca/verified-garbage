module

public import VerifiedGarbage.Impl.AesXts.X86_64Fn
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
public import VerifiedGarbage.Spec.Xts.Contract
public import VerifiedGarbage.Spec.Xts.OutOfPlace
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueScrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Run
public import VerifiedGarbage.Proof.AesXts.X86_64.Variant
import VerifiedGarbage.Proof.Aes.X86_64.ModesScrub
import VerifiedGarbage.Proof.Aes.ScrubLocal
public import VerifiedGarbage.Proof.AesXts.X86_64.UnitTo.Crypt
import VerifiedGarbage.Proof.AesXts.X86_64.CT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.AesXts.X86_64.UnitTo.Crypt
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesXts.X86_64.CT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.AesCbc.X86_64.Loop
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.AesXts.X86_64.Unit.Run
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Body
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.AesXts.Unit
meta import VerifiedGarbage.Proof.AesXts.X86_64.Variant
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.AesCbc.X86_64.Loop

/-! ### `AesXts.X86_64.UnitTo.Verified`, which only this module used -/

section

/-! ### `AesXts.X86_64.Unit.CT`, which this module and modules that import it used -/

section

/-! ### `AesXts.X86_64.Unit.Dec`, which this module and modules that import it used -/

section

/-! ### `AesXts.X86_64.Unit.Enc`, which this module and modules that import it used -/

section

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
  · rw [gpr_setReg_of_ne _ _ (by decide), rdx₁, hr12, hrax, last_eq _ hp.m_pos (by have := hp.m_lt; omega_using [this])]
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
        (hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega_using [hi]) (by omega_using [hb, hi])))))
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
      · exact hp.stk_data.symm.sub_left hp.tl_sub) (by omega_using [hb])
  · rw [Proof.AesXts.Unit.crypt_one_of c.out,
      hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp), m₂,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left (sub_trans t_sub s_sub)).sub_right hp.lb_sub) (by decide), htw]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_using [])) hp.hd_l
      (sub_trans t_sub s_sub) h.inv.rsp c (by dsimp only; have := hp.wrapD; omega_using [this]), m₂]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega_using [this])
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l (sub_trans t_sub s_sub) h.inv.rsp c
      (by dsimp only; omega_using [hb]), m₂]

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
    (by rw [len_eq s₀]; omega_using []) (by rw [rdi₂, h.inv.rbx]) (by rw [rsi₂, h.inv.rbp, rsi_ofNat])
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
  refine WP.seq (WP.mono (blocks_call hp true v.encOk v.encNosp v.encDepth (by rw [len_eq s₀]; omega_using []) h₂.tw
    h₂.pre) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (splitAll_wp hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) h₄.zf (fun hb => WP.block_nil (whole_fin h₄.all (by simpa using hb)))
    (fun hb => encSteal_wp hp v h₄ (by simpa using hb))) fun s₅ h₅ => ?_)
  exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.X86_64.Unit

end

end

/-!
# XTS-AES of data units on x86-64: decryption

`decrypt_wp`: the tweak, then without a partial block the call on the whole
blocks; otherwise the call on all but the last whole block, the next tweak
(that of block `M`, `nextT`), the call on the last whole block from it, the
swap, and the call on the last whole block from the tweak of block `M - 1`;
then the epilogue, for any implementation `v` of the whole-block functions.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Unit

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesXts.X86_64Unit
open VG.Proof.AesCbc.X86_64 (modeX86_64 in_rw)
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- Before the call on the last whole block from the tweak of block `M`,
which is at `zO`. -/
structure DecL1 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (Zp s₀) (L s₀) (S s₀) 1 (R s₀)
  mem : ∃ m, AllMem false s₀ (M s₀ - 1) m ∧ Frame [⟨Zp s₀, 16⟩] m s.mem ∧
    bytesAt s.mem (Zp s₀) 16 = Spec.Xts.mulAlpha (bytesAt m (Tp s₀) 16)

/-- The memory after the call on the last whole block from the tweak of
block `M`: `PP` there, from the memory `m` after the first `M - 1` blocks. -/
def DecMem (s₀ : State) (m₅ : Mem) : Prop :=
  ∃ m, AllMem false s₀ (M s₀ - 1) m ∧
    bytesAt m₅ (L s₀) 16 = Spec.Xts.block (ciph s₀ false) (Spec.Xts.next (t0 s₀) (M s₀)) (bytesAt m (L s₀) 16) ∧
    bytesAt m₅ (D s₀) (16 * (M s₀ - 1)) = bytesAt m (D s₀) (16 * (M s₀ - 1)) ∧
    bytesAt m₅ (L s₀ + 16) (B s₀) = bytesAt m (L s₀ + 16) (B s₀) ∧
    bytesAt m₅ (Tp s₀) 16 = Spec.Xts.next (t0 s₀) (M s₀ - 1)

/-- After the call on the last whole block from the tweak of block `M`. -/
structure DecL2 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  mem : DecMem s₀ s.mem

/-- Before the call on the last whole block from the tweak of block `M - 1`:
`Pₘ` and `CC` swapped into place. -/
structure DecL3 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (Tp s₀) (L s₀) (S s₀) 1 (R s₀)
  mem : ∃ m₅, DecMem s₀ m₅ ∧ s.mem = swapMem m₅ (L s₀) (B s₀)

/-- The arguments of the call on all but the last whole block. -/
theorem argsHead_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsHead) s (BlocksReady s₀ (M s₀ - 1)) := by
  have hm := hp.m_pos
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, cs₁, mem₁, rd₁, wr₁⟩ :=
    argsHead_ok s (by rw [h.inv.r13]; exact hm)
  have h₁ := TwPost.keep hp h cs₁ mem₁ rd₁ wr₁
  exact WP.of_runBlock ⟨s₁, run₁, h₁, xpre_blocks hp h₁.inv.rd h₁.inv.wr h₁.inv.rsp (N := M s₀ - 1)
    (by rw [len_eq s₀]; omega_arith) (by rw [rdi₁, h.inv.rbx]) (by rw [rsi₁, h.inv.rbp, rsi_ofNat])
    (by rw [rdx₁, h.inv.r15]) (by rw [rcx₁, h.inv.r12]) (by rw [r8₁, h.inv.r13]) (by rw [r9₁, h.inv.r15])⟩

/-- The tweak of block `M`, at `zO`, and the arguments of the call on the
last whole block from it. -/
theorem decL1_wp {s₂ : State} (h₂ : AllPost false s₀ (M s₀ - 1) s₂) :
    WP isa (.block (nextT ++ split ++ lastAddr ++ argsL zO)) s₂ (DecL1 s₀) := by
  have hm := hp.m_pos
  have wr₂ : s₂.wr = [dataR s₀, scrR s₀] := by rw [h₂.inv.wr, hp.wr]
  have rdwr₂ : s₂.rd ++ s₂.wr = [schR s₀, tschR s₀, iR s₀, argR s₀, dataR s₀, scrR s₀] := by
    rw [h₂.inv.rd, h₂.inv.wr, hp.rd, hp.wr]; rfl
  obtain ⟨s₃, run₃, g₃, f₃, z₃, rd₃, wr₃⟩ := nextT_ok s₂ (T := Tp s₀) (Z := Zp s₀) (by rw [h₂.inv.r15])
    (by rw [h₂.inv.r15, ← Offset.add_add]) (by rw [h₂.inv.r15]) (by rw [h₂.inv.r15, ← Offset.add_add])
    (by rw [rdwr₂]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by rw [rdwr₂, Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [tO])))
    (by rw [wr₂]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))
    (by rw [wr₂, Offset.add_add]; exact in_rw (r := scrR s₀) (by simp) (cS s₀ _ _ (by simp [zO])))
  have inv₃ : Inv s₀ s₃ := Inv.step hp h₂.inv (rs := [⟨Zp s₀, 16⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl z_sub)) f₃
    (fun r hr => g₃ r (pinned_ne hr).1 (pinned_ne hr).2.1 (pinned_ne hr).2.2.1) rd₃ wr₃
  rw [List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [WP.block_append_iff]
  refine split_wp inv₃ fun s₄ rax₄ _ _ g₄ mem₄ rd₄ wr₄ => ?_
  rw [WP.block_append_iff]
  obtain ⟨s₅, run₅, rdx₅, g₅, mem₅, rd₅, wr₅⟩ := lastAddr_ok s₄
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  obtain ⟨s₆, run₆, rdi₆, rsi₆, rdx₆, rcx₆, r8₆, r9₆, cs₆, mem₆, rd₆, wr₆⟩ := argsL_ok s₅ (o := zO) rfl
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have k₆ (r : Reg) (hr : r ∈ pinned) : s₆.gpr r = s₃.gpr r := by
    have n := pinned_ne hr
    rw [cs₆ r (pinned_cs r hr), g₅ r n.2.2.1, g₄ r n.1 n.2.2.2.1]
  have m₆ : s₆.mem = s₃.mem := by rw [mem₆, mem₅, mem₄]
  have inv₆ : Inv s₀ s₆ := Inv.step hp inv₃ (rs := []) (fun _ h => by simp at h)
    (by rw [m₆]; exact Frame.refl _ _) k₆ (by rw [rd₆, rd₅, rd₄]) (by rw [wr₆, wr₅, wr₄])
  refine ⟨inv₆, xpre_last hp inv₆.rd inv₆.wr inv₆.rsp (.inr rfl) (by rw [rdi₆, g₅ _ (by decide), g₄ _ (by decide)
      (by decide), inv₃.rbx]) (by rw [rsi₆, g₅ _ (by decide), g₄ _ (by decide) (by decide), inv₃.rbp, rsi_ofNat])
    (by rw [rdx₆, g₅ _ (by decide), g₄ _ (by decide) (by decide), inv₃.r15])
    (by rw [rcx₆, rdx₅, g₄ _ (by decide) (by decide), rax₄, inv₃.r12,
      last_eq _ hm (by have := hp.m_lt; omega_arith)]) r8₆
    (by rw [r9₆, g₅ _ (by decide), g₄ _ (by decide) (by decide), inv₃.r15]),
    ⟨s₂.mem, h₂.mem, by rw [m₆]; exact f₃, by rw [m₆]; exact z₃⟩⟩

/-- The call on the last whole block from the tweak of block `M`. -/
theorem decL2_wp (v : XtsImpl) {s : State} (h : DecL1 s₀ s) :
    WP isa (.call v.dec.name v.dec.code) s (DecL2 s₀) := by
  have hm := hp.m_pos
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨m, ⟨hout, htw, hfr⟩, f₃, z₃⟩ := h.mem
  refine WP.mono (xts_call false v.decOk v.decNosp v.decDepth h.pre) fun s₇ c₇ => ?_
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub s_sub
  have zL : Region.Sub ⟨Zp s₀, 16⟩ (scrR s₀) := sub_trans z_sub s_sub
  have eW := hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)
  refine ⟨Inv.call hp h.inv z_sub (.inl hp.l_sub) c₇, m, ⟨hout, htw, hfr⟩, ?_, ?_, ?_, ?_⟩
  · rw [Proof.AesXts.Unit.crypt_one_of c₇.out, eW, z₃, htw, ← Proof.AesXts.next_succ,
      Nat.sub_add_cancel hm,
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.sub_left hp.l_sub).sub_right zL) (by decide)]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_arith)) hp.hd_l zL h.inv.rsp c₇
      (by dsimp only; have := hp.wrapD; omega_arith)]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left (blocks_sub (by omega_arith))).sub_right zL) (by dsimp only; have := hp.wrapD; omega_arith)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l zL h.inv.rsp c₇ (by dsimp only; omega_arith)]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left hp.tl_sub).sub_right zL) (by dsimp only; omega_arith)
  · rw [Proof.Cmac.bytesAt_frame c₇.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hp.t_z
        · exact (hp.data_scr.symm.sub_left tL).sub_right hp.l_sub
        · exact hp.t_wk
        · rw [stk, h.inv.rsp]; exact (hp.stk_scr.sub_right tL).symm) (by decide),
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), htw]

/-- `Pₘ` and `CC` swapped into place, and the arguments of the call on the
last whole block from the tweak of block `M - 1`. -/
theorem decL3_wp {s : State} (h : DecL2 s₀ s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block (split ++ stealPre)) swap) (.block (argsL tO))) s (DecL3 s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff]
  refine split_wp h.inv fun s₈ rax₈ r8₈ _ g₈ mem₈ rd₈ wr₈ => ?_
  refine stealPre_wp hp (by rw [g₈ _ (by decide) (by decide), h.inv.r12]) rax₈
    fun s₉ rdx₉ rcx₉ g₉ mem₉ rd₉ wr₉ => ?_
  have wr₉' : s₉.wr = [dataR s₀, scrR s₀] := by rw [wr₉, wr₈, h.inv.wr, hp.wr]
  refine WP.mono (swap_ok s₉ (Nat.pos_of_ne_zero hB) hb rdx₉ rcx₉
    (by rw [g₉ _ (by decide) (by decide), r8₈]) (fun i hi => by
      rw [wr₉']
      exact in_rw (r := dataR s₀) (by simp)
        (hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega_arith) (by omega_arith)))))
    fun s₁₀ ⟨mem₁₀, g₁₀, rd₁₀, wr₁₀⟩ => ?_
  obtain ⟨s₁₁, run₁₁, rdi₁₁, rsi₁₁, rdx₁₁, rcx₁₁, r8₁₁, r9₁₁, cs₁₁, mem₁₁, rd₁₁, wr₁₁⟩ := argsL_ok s₁₀ (o := tO) rfl
  refine WP.of_runBlock ⟨s₁₁, run₁₁, ?_⟩
  have k₁₀ (r : Reg) (hr : r ∈ pinned) : s₁₀.gpr r = s.gpr r := by
    have n := pinned_ne hr
    rw [g₁₀ r n.1 n.2.2.2.2 n.2.1, g₉ r n.2.2.1 n.2.1, g₈ r n.1 n.2.2.2.1]
  have m₁₀ : s₁₀.mem = swapMem s.mem (L s₀) (B s₀) := by rw [mem₁₀, mem₉, mem₈]
  have inv₁₀ : Inv s₀ s₁₀ := Inv.step hp h.inv (rs := [⟨L s₀, 16 + B s₀⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl hp.lb_sub)
    (by rw [m₁₀]; exact Proof.AesXts.Unit.swapMem_frame _ _ _) k₁₀ (by rw [rd₁₀, rd₉, rd₈])
    (by rw [wr₁₀, wr₉, wr₈])
  have inv₁₁ : Inv s₀ s₁₁ := Inv.step hp inv₁₀ (rs := []) (fun _ h => by simp at h)
    (by rw [mem₁₁]; exact Frame.refl _ _) (fun r hr => cs₁₁ r (pinned_cs r hr)) rd₁₁ wr₁₁
  exact ⟨inv₁₁, xpre_last hp inv₁₁.rd inv₁₁.wr inv₁₁.rsp (.inl rfl) (by rw [rdi₁₁, inv₁₀.rbx])
    (by rw [rsi₁₁, inv₁₀.rbp, rsi_ofNat]) (by rw [rdx₁₁, inv₁₀.r15])
    (by rw [rcx₁₁, g₁₀ _ (by decide) (by decide) (by decide), rdx₉]) r8₁₁ (by rw [r9₁₁, inv₁₀.r15]),
    s.mem, h.mem, by rw [mem₁₁, m₁₀]⟩

/-- The call on the last whole block from the tweak of block `M - 1`, and
the data unit's plaintext. -/
theorem decLast_wp (v : XtsImpl) {s : State} (h : DecL3 s₀ s) (hB : B s₀ ≠ 0) :
    WP isa (.call v.dec.name v.dec.code) s (Fin false s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  have hm := hp.m_pos
  obtain ⟨m₅, ⟨m, ⟨hout, htw, hfr⟩, h5L, h5H, h5T, tw₅⟩, m₁₀⟩ := h.mem
  refine WP.mono (xts_call false v.decOk v.decNosp v.decDepth h.pre) fun s₁₂ c₁₂ => ?_
  refine ⟨Inv.call hp h.inv t_sub (.inl hp.l_sub) c₁₂, ?_⟩
  have sw := Proof.AesXts.Unit.swapMem_frame m₅ (L s₀) (B s₀)
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub s_sub
  have eW' := hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.dec_steal (m₃ := m) (m₅ := m₅) hm (Nat.pos_of_ne_zero hB) hb hout
    ⟨?_, ?_⟩ ⟨h5L, h5H, h5T⟩ ⟨?_, ?_, ?_⟩
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.l_hd
      · exact hp.data_scr.sub_left hp.l_sub
      · exact hp.stk_data.symm.sub_left hp.l_sub) (by decide)
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.hd_tl.symm
      · exact hp.data_scr.sub_left hp.tl_sub
      · exact hp.stk_data.symm.sub_left hp.tl_sub) (by omega_arith)
  · rw [Proof.AesXts.Unit.crypt_one_of c₁₂.out, eW', m₁₀,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left tL).sub_right hp.lb_sub) (by decide), tw₅]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_arith)) hp.hd_l tL h.inv.rsp c₁₂
      (by dsimp only; have := hp.wrapD; omega_arith), m₁₀]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega_arith)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l tL h.inv.rsp c₁₂ (by dsimp only; omega_arith), m₁₀]

/-- The steal of decryption, after the tweak. -/
theorem decSteal_wp (v : XtsImpl) {s : State} (h : TwPost s₀ s) (hB : B s₀ ≠ 0) :
    WP isa (decSteal v.dec) s (Fin false s₀) := by
  refine WP.seq (WP.mono (argsHead_wp hp h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (blocks_call hp false v.decOk v.decNosp v.decDepth (by rw [len_eq s₀]; omega_arith) h₁.tw
    h₁.pre) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (decL1_wp hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (decL2_wp hp v h₃) fun s₄ h₄ => ?_)
  exact WP.assoc (WP.assoc (WP.seq (WP.mono (decL3_wp hp h₄ hB) fun _ h₅ => decLast_wp hp v h₅ hB)))

theorem split_tw_wp {s : State} (h : TwPost s₀ s) :
    WP isa (.block split) s fun s' => TwPost s₀ s' ∧ s'.zf = some (decide (B s₀ = 0)) :=
  split_wp h.inv fun _ _ _ zf₂ g₂ mem₂ rd₂ wr₂ =>
    ⟨TwPost.keep hp h (fun r hr => g₂ r (AesCbc.X86_64.calleeSaved_ne_rax hr) (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)) mem₂ rd₂ wr₂, zf₂⟩

theorem decrypt_wp (v : XtsImpl) :
    WP isa (Impl.AesXts.X86_64Unit.decrypt v.xts) s₀ fun s' => gprPreserved s₀ s' ∧ (unitX86_64 false).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp v.encOk v.encNosp v.encDepth) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (split_tw_wp hp h₁) fun s₂ ⟨h₂, zf₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) zf₂ (fun hb => ?_)
    (fun hb => decSteal_wp hp v h₂ (by simpa using hb))) fun s₅ h₅ => ?_)
  · refine WP.seq (WP.mono (argsAll_wp hp h₂) fun s₃ h₃ => ?_)
    exact WP.mono (blocks_call hp false v.decOk v.decNosp v.decDepth (by rw [len_eq s₀]; omega_arith) h₃.tw h₃.pre)
      fun s₄ h₄ => whole_fin h₄ (by simpa using hb)
  · exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.X86_64.Unit

end

end

/-!
# XTS-AES of data units on x86-64: constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`), from the correctness proof's states between the pieces: the
taint analysis covers the code between the calls (the swap's loop with
them), from the registers the states pin to public values (`Inv.agree`),
each call is constant time by its callee's proof (`xcall_rel`), and the one
branch, on whether there is a partial block, agrees in both runs.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Unit

open VG VG.X86_64 VG.Impl.AesXts.X86_64Unit
open VG.Proof.AesCbc.X86_64 (modeX86_64)

/-- A call of a whole-block function, with the same arguments in both runs,
and what each run leaves. -/
theorem xcall_rel (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s s')
    (ct : ConstantTime isa (modeX86_64 (AesXts.xtsMode enc)).pre (modeX86_64 (AesXts.xtsMode enc)).pub c)
    {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hx : ∀ s₁ s₂, P s₁ s₂ → ∃ W T D S : Addr, ∃ N R : Nat,
      XPre s₁ W T D S N R ∧ XPre s₂ W T D S N R ∧ s₁.gpr .rsp = s₂.gpr .rsp)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa (.call n c) s₁ F₁ ∧ WP isa (.call n c) s₂ F₂) :
    RelCT isa P (.call n c) fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ :=
  ((xts_rel enc ok ct hx).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

section
variable {s₀ s₀' : State} (hq : unitPub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_K : K s₀ = K s₀' := hq.2.1
theorem pub_rdx : s₀.gpr .rdx = s₀'.gpr .rdx := hq.2.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_rdx hq]
theorem pub_D : D s₀ = D s₀' := hq.2.2.2.2.1
theorem pub_r9 : s₀.gpr .r9 = s₀'.gpr .r9 := hq.2.2.2.2.2.1
theorem pub_rsp : s₀.gpr .rsp = s₀'.gpr .rsp := hq.2.2.2.2.2.2.1
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.2.2
theorem pub_M : M s₀ = M s₀' := by rw [M, M, Len, Len, pub_r9 hq]
theorem pub_B : B s₀ = B s₀' := by rw [B, B, Len, Len, pub_r9 hq]
theorem pub_L : L s₀ = L s₀' := by rw [L, L, pub_D hq, pub_M hq]
theorem pub_Tp : Tp s₀ = Tp s₀' := by simp only [Tp, pub_S hq]
theorem pub_Zp : Zp s₀ = Zp s₀' := by simp only [Zp, pub_S hq]

theorem Inv.agree {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) : ∀ r ∈ pinned, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.rbx, h₂.rbx, pub_W hq]
  · rw [h₁.rbp, h₂.rbp, pub_rdx hq]
  · rw [h₁.r12, h₂.r12, pub_D hq]
  · rw [h₁.r13, h₂.r13, pub_r9 hq]
  · rw [h₁.r15, h₂.r15, pub_S hq]
  · rw [h₁.rsp, h₂.rsp, pub_rsp hq]

omit hq in
/-- Agreement on the pinned registers and more. -/
theorem agree_cons {s₁ s₂ : State} {rs : List Reg} (h : ∀ r ∈ pinned, s₁.gpr r = s₂.gpr r)
    (h' : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : ∀ r ∈ rs ++ pinned, s₁.gpr r = s₂.gpr r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h' r hr
  · exact h r hr

end

/-! ## Taint checks -/

theorem ldS_taint : ∃ h, (taint.check (Taint.ofRegs [.rsp]) (.block ldS) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem pro_taint : ∃ h, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
    (.block pro) h).isSome = true := ⟨_, by taint_decide⟩

theorem argsAll_taint : ∃ h, (taint.check (Taint.ofRegs pinned) (.block argsAll) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem argsHead_taint : ∃ h, (taint.check (Taint.ofRegs pinned) (.block argsHead) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem split_taint : ∃ h, (taint.check (Taint.ofRegs pinned) (.block split) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encLast_taint : ∃ h, (taint.check (Taint.ofRegs (([.rax, .r8] : List Reg) ++ pinned))
    (.seq (.seq (.block stealPre) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL1_taint : ∃ h, (taint.check (Taint.ofRegs pinned)
    (.block (nextT ++ split ++ lastAddr ++ argsL zO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL3_taint : ∃ h, (taint.check (Taint.ofRegs pinned)
    (.seq (.seq (.block (split ++ stealPre)) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.r15]) (.block restore) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## The two runs -/

section
variable {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : unitPub s₀ s₀')
include hp hp' hq

theorem tweak_rel (v : XtsImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (tweak v.enc) fun a b => TwPost s₀ a ∧ TwPost s₀' b := by
  have l := taint_rel [.rsp] ldS_taint (P := fun a b => a = s₀ ∧ b = s₀')
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.mem_singleton] at hr; subst hr; exact pub_rsp hq)
    (F₁ := fun s => s = s₀.setReg .rax (S s₀)) (F₂ := fun s => s = s₀'.setReg .rax (S s₀'))
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨ldS_wp hp, ldS_wp hp'⟩
  have p := taint_rel [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] pro_taint
    (P := fun a b => a = s₀.setReg .rax (S s₀) ∧ b = s₀'.setReg .rax (S s₀'))
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h
      have hq' := hq
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_self, pub_S hq]
      all_goals rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide)]
      all_goals with_reducible assumption)
    (F₁ := ProPost s₀) (F₂ := ProPost s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨pro_wp hp, pro_wp hp'⟩
  have c := xcall_rel true v.encOk v.encCt (n := v.enc.name) (P := fun a b => ProPost s₀ a ∧ ProPost s₀' b)
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
      rw [pub_K hq, pub_Zp hq, pub_Tp hq, pub_S hq, pub_R hq]; exact h.2.pre,
      by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
    (F₁ := TwPost s₀) (F₂ := TwPost s₀')
    (fun a b h => ⟨tcall_wp hp v.encOk v.encNosp v.encDepth h.1, tcall_wp hp' v.encOk v.encNosp v.encDepth h.2⟩)
  exact (l.mono (fun _ _ h => h) fun _ _ h => h).seq (p.seq c)

theorem blocks_rel (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (modeX86_64 (AesXts.xtsMode enc)).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeX86_64 (AesXts.xtsMode enc)).post s s')
    (ct : ConstantTime isa (modeX86_64 (AesXts.xtsMode enc)).pre (modeX86_64 (AesXts.xtsMode enc)).pub c)
    (nosp : NoSp c) (depth : c.depth ≤ 1) {N N' : Nat} (hN : 16 * N ≤ Len s₀) (hN' : 16 * N' ≤ Len s₀')
    (hNN : N = N') :
    RelCT isa (fun a b => BlocksReady s₀ N a ∧ BlocksReady s₀' N' b) (.call n c)
      fun a b => AllPost enc s₀ N a ∧ AllPost enc s₀' N' b :=
  xcall_rel enc ok ct
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
      rw [pub_W hq, pub_Tp hq, pub_D hq, pub_S hq, hNN, pub_R hq]; exact h.2.pre,
      by rw [h.1.tw.inv.rsp, h.2.tw.inv.rsp, pub_rsp hq]⟩)
    fun a b h => ⟨blocks_call hp enc ok nosp depth hN h.1.tw h.1.pre, blocks_call hp' enc ok nosp depth hN' h.2.tw h.2.pre⟩

theorem restore_rel {enc : Bool} :
    RelCT isa (fun a b => Fin enc s₀ a ∧ Fin enc s₀' b) (.block restore) fun _ _ => True :=
  (taint_rel [.r15] restore_taint (P := fun a b => Fin enc s₀ a ∧ Fin enc s₀' b)
    (fun a b h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.inv.r15, h.2.inv.r15, pub_S hq])
    (F₁ := fun _ => True) (F₂ := fun _ => True)
    fun a b h => ⟨WP.mono (fin_wp hp h.1.inv) fun _ _ => trivial, WP.mono (fin_wp hp' h.2.inv) fun _ _ => trivial⟩).mono
    (fun _ _ h => h) fun _ _ _ => trivial

theorem encrypt_rel (v : XtsImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (Impl.AesXts.X86_64Unit.encrypt v.xts) fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq v
  have a := taint_rel pinned argsAll_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀)) (F₂ := BlocksReady s₀' (M s₀'))
    fun a b h => ⟨argsAll_wp hp h.1, argsAll_wp hp' h.2⟩
  have c := blocks_rel hp hp' hq true v.encOk v.encCt v.encNosp v.encDepth (by rw [len_eq s₀]; omega_using [])
    (by rw [len_eq s₀']; omega_using []) hM (n := v.enc.name)
  have sp := taint_rel pinned split_taint (P := fun a b => AllPost true s₀ (M s₀) a ∧ AllPost true s₀' (M s₀') b)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := SplitPost true s₀ (M s₀))
    (F₂ := SplitPost true s₀' (M s₀')) fun a b h => ⟨splitAll_wp hp h.1, splitAll_wp hp' h.2⟩
  have br : RelCT isa (fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
      (.ite .e (.block []) (encSteal v.enc)) fun a b => Fin true s₀ a ∧ Fin true s₀' b := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.zf, h.2.zf, pub_B hq]
    · refine RelCT.block_nil fun a b h => ?_
      have hb : B s₀ = 0 := by
        have := h.2; change a.zf = _ at this; rw [h.1.1.zf] at this; simpa using this
      exact ⟨whole_fin h.1.1.all hb, whole_fin h.1.2.all (by rw [← pub_B hq]; exact hb)⟩
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b =>
          SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; change a.zf = _ at this; rw [h.1.1.zf] at this; simpa using this, h.1⟩)
        fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      refine RelCT.assoc (RelCT.assoc ?_)
      have l := taint_rel ([.rax, .r8] ++ pinned) encLast_taint
        (P := fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
        (fun a b h => agree_cons (Inv.agree hq h.1.all.inv h.2.all.inv) fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h.1.rax, h.2.rax, hM]
          · rw [h.1.r8, h.2.r8, pub_B hq])
        (F₁ := EncLast s₀) (F₂ := EncLast s₀') fun a b h => ⟨encLast_wp hp h.1 hB, encLast_wp hp' h.2 hB'⟩
      have c := xcall_rel true v.encOk v.encCt (n := v.enc.name) (P := fun a b => EncLast s₀ a ∧ EncLast s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Tp hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.pre,
          by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
        (F₁ := Fin true s₀) (F₂ := Fin true s₀')
        fun a b h => ⟨encLastCall_wp hp v h.1 hB, encLastCall_wp hp' v h.2 hB'⟩
      exact l.seq c
  exact t.seq (a.seq (c.seq (sp.seq (br.seq (restore_rel hp hp' hq)))))

theorem decrypt_rel (v : XtsImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (Impl.AesXts.X86_64Unit.decrypt v.xts) fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq v
  have sp := taint_rel pinned split_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv)
    (F₁ := fun s => TwPost s₀ s ∧ s.zf = some (decide (B s₀ = 0)))
    (F₂ := fun s => TwPost s₀' s ∧ s.zf = some (decide (B s₀' = 0)))
    fun a b h => ⟨split_tw_wp hp h.1, split_tw_wp hp' h.2⟩
  have br : RelCT isa (fun a b => (TwPost s₀ a ∧ a.zf = some (decide (B s₀ = 0))) ∧
      (TwPost s₀' b ∧ b.zf = some (decide (B s₀' = 0))))
      (.ite .e (.seq (.block argsAll) (.call v.dec.name v.dec.code)) (decSteal v.dec))
      fun a b => Fin false s₀ a ∧ Fin false s₀' b := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.2, h.2.2, pub_B hq]
    · refine (RelCT.exists_ (P := fun (_ : B s₀ = 0) a b => TwPost s₀ a ∧ TwPost s₀' b) fun hb => ?_).mono
        (fun a b h => ⟨by have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hb' : B s₀' = 0 := by rw [← pub_B hq]; exact hb
      have a := taint_rel pinned argsAll_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀))
        (F₂ := BlocksReady s₀' (M s₀')) fun a b h => ⟨argsAll_wp hp h.1, argsAll_wp hp' h.2⟩
      have c := blocks_rel hp hp' hq false v.decOk v.decCt v.decNosp v.decDepth (by rw [len_eq s₀]; omega_using [])
        (by rw [len_eq s₀']; omega_using []) hM (n := v.dec.name)
      exact a.seq (c.mono (fun _ _ h => h) fun _ _ h => ⟨whole_fin h.1 hb, whole_fin h.2 hb'⟩)
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b => TwPost s₀ a ∧ TwPost s₀' b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      have a := taint_rel pinned argsHead_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀ - 1))
        (F₂ := BlocksReady s₀' (M s₀' - 1)) fun a b h => ⟨argsHead_wp hp h.1, argsHead_wp hp' h.2⟩
      have c₁ := blocks_rel hp hp' hq false v.decOk v.decCt v.decNosp v.decDepth (N := M s₀ - 1)
        (N' := M s₀' - 1) (by rw [len_eq s₀]; omega_using []) (by rw [len_eq s₀']; omega_using []) (by rw [hM]) (n := v.dec.name)
      have l₁ := taint_rel pinned decL1_taint
        (P := fun a b => AllPost false s₀ (M s₀ - 1) a ∧ AllPost false s₀' (M s₀' - 1) b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL1 s₀) (F₂ := DecL1 s₀')
        fun a b h => ⟨decL1_wp hp h.1, decL1_wp hp' h.2⟩
      have c₂ := xcall_rel false v.decOk v.decCt (n := v.dec.name) (P := fun a b => DecL1 s₀ a ∧ DecL1 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Zp hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.pre,
          by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
        (F₁ := DecL2 s₀) (F₂ := DecL2 s₀') fun a b h => ⟨decL2_wp hp v h.1, decL2_wp hp' v h.2⟩
      have l₃ := taint_rel pinned decL3_taint (P := fun a b => DecL2 s₀ a ∧ DecL2 s₀' b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL3 s₀) (F₂ := DecL3 s₀')
        fun a b h => ⟨decL3_wp hp h.1 hB, decL3_wp hp' h.2 hB'⟩
      have c₃ := xcall_rel false v.decOk v.decCt (n := v.dec.name) (P := fun a b => DecL3 s₀ a ∧ DecL3 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Tp hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.pre,
          by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
        (F₁ := Fin false s₀) (F₂ := Fin false s₀') fun a b h => ⟨decLast_wp hp v h.1 hB, decLast_wp hp' v h.2 hB'⟩
      exact a.seq (c₁.seq (l₁.seq (c₂.seq (RelCT.assoc (RelCT.assoc (l₃.seq c₃))))))
  exact t.seq (sp.seq (br.seq (restore_rel hp hp' hq)))

end

theorem encrypt_ct (v : XtsImpl) :
    ConstantTime isa (unitX86_64 true).pre (unitX86_64 true).pub (Impl.AesXts.X86_64Unit.encrypt v.xts) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel (UPre.of h₁) (UPre.of h₂) hq v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decrypt_ct (v : XtsImpl) :
    ConstantTime isa (unitX86_64 false).pre (unitX86_64 false).pub (Impl.AesXts.X86_64Unit.decrypt v.xts) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel (UPre.of h₁) (UPre.of h₂) hq v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesXts.X86_64.Unit

end

end

/-!
# XTS-AES of data units out of place on x86-64: constant time and `Verified`

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`), from the correctness proof's states between the pieces, as
in place (`Unit/CT.lean`): the taint analysis covers the code between the
calls (the copy and the swap's loop with them), from the registers the
states pin to public values (`Inv.agree`), each call is constant time by its
callee's proof, and the one branch, on whether there is a partial block,
agrees in both runs. Correctness and constant time give `Verified` for the
shared contracts of `Spec/Xts/OutOfPlace.lean`, with 24 bytes of stack (the
return addresses of the out-of-place whole-block function, of its call of
an in-place one, and of that one's call of a block function).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.UnitTo

open VG VG.X86_64 VG.Impl.AesXts.X86_64Unit
open VG.Impl.AesXts.X86_64UnitTo renaming ldS → ldSTo, setup → setupTo, pro → proTo, tweak → tweakTo,
  argsAll → argsAllTo, argsHead → argsHeadTo, encrypt → encryptTo, decrypt → decryptTo
open VG.Impl.AesXts.X86_64UnitTo (copyRest wholeBytes headBytes decStealTail)
open VG.Proof.AesCbc.X86_64 (modeX86_64)
open VG.Proof.AesXts.X86_64 (taint_rel)
open VG.Proof.AesXts.X86_64.To (xtsToX86_64 XtPre xtsTo_rel)
open VG.Proof.AesXts.X86_64.Unit (xcall_rel)

/-- An out-of-place call, with the same arguments in both runs, and what each
run leaves. -/
theorem xtcall_rel (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (xtsToX86_64 enc).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xtsToX86_64 enc).post s s')
    (ct : ConstantTime isa (xtsToX86_64 enc).pre (xtsToX86_64 enc).pub c)
    {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hx : ∀ s₁ s₂, P s₁ s₂ → ∃ W T Sr D S : Addr, ∃ N R : Nat,
      XtPre s₁ W T Sr D S N R ∧ XtPre s₂ W T Sr D S N R ∧ s₁.gpr .rsp = s₂.gpr .rsp)
    (hw : ∀ s₁ s₂, P s₁ s₂ → WP isa (.call n c) s₁ F₁ ∧ WP isa (.call n c) s₂ F₂) :
    RelCT isa P (.call n c) fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂ :=
  ((xtsTo_rel enc ok ct hx).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

section
variable {s₀ s₀' : State} (hq : unitPub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_K : K s₀ = K s₀' := hq.2.1
theorem pub_rdx : s₀.gpr .rdx = s₀'.gpr .rdx := hq.2.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_rdx hq]
theorem pub_Sr : Sr s₀ = Sr s₀' := hq.2.2.2.2.1
theorem pub_r9 : s₀.gpr .r9 = s₀'.gpr .r9 := hq.2.2.2.2.2.1
theorem pub_rsp : s₀.gpr .rsp = s₀'.gpr .rsp := hq.2.2.2.2.2.2.1
theorem pub_D : D s₀ = D s₀' := hq.2.2.2.2.2.2.2.1
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.2.2.2.2
theorem pub_M : M s₀ = M s₀' := by rw [M, M, Len, Len, pub_r9 hq]
theorem pub_B : B s₀ = B s₀' := by rw [B, B, Len, Len, pub_r9 hq]
theorem pub_L : L s₀ = L s₀' := by rw [L, L, pub_D hq, pub_M hq]
theorem pub_Tp : Tp s₀ = Tp s₀' := by simp only [Tp, pub_S hq]
theorem pub_Zp : Zp s₀ = Zp s₀' := by simp only [Zp, pub_S hq]

theorem Inv.agree {s₁ s₂ : State} (h₁ : Inv s₀ s₁) (h₂ : Inv s₀' s₂) : ∀ r ∈ pinned, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.rbx, h₂.rbx, pub_W hq]
  · rw [h₁.rbp, h₂.rbp, pub_rdx hq]
  · rw [h₁.r12, h₂.r12, pub_D hq]
  · rw [h₁.r13, h₂.r13, pub_r9 hq]
  · rw [h₁.r14, h₂.r14, pub_Sr hq]
  · rw [h₁.r15, h₂.r15, pub_S hq]
  · rw [h₁.rsp, h₂.rsp, pub_rsp hq]

omit hq in
/-- Agreement on the pinned registers and more. -/
theorem agree_cons {s₁ s₂ : State} {rs : List Reg} (h : ∀ r ∈ pinned, s₁.gpr r = s₂.gpr r)
    (h' : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : ∀ r ∈ rs ++ pinned, s₁.gpr r = s₂.gpr r := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact h' r hr
  · exact h r hr

end

/-! ## Taint checks -/

theorem ldS_taint : ∃ h, (taint.check (Taint.ofRegs [.rsp]) (.block ldSTo) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem pro_taint : ∃ h, (taint.check (Taint.ofRegs [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
    (.block proTo) h).isSome = true := ⟨_, by taint_decide⟩

theorem argsAll_taint : ∃ h, (taint.check (Taint.ofRegs pinned) (.block argsAllTo) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem argsHead_taint : ∃ h, (taint.check (Taint.ofRegs pinned) (.block argsHeadTo) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem copyAll_taint : ∃ h, (taint.check (Taint.ofRegs pinned) (.seq (.block wholeBytes) copyRest) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem copyHead_taint : ∃ h, (taint.check (Taint.ofRegs pinned) (.seq (.block headBytes) copyRest) h).isSome =
    true := ⟨_, by taint_decide⟩

theorem split_taint : ∃ h, (taint.check (Taint.ofRegs pinned) (.block split) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encLast_taint : ∃ h, (taint.check (Taint.ofRegs (([.rax, .r8] : List Reg) ++ pinned))
    (.seq (.seq (.block stealPre) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL1_taint : ∃ h, (taint.check (Taint.ofRegs pinned)
    (.block (nextT ++ split ++ lastAddr ++ argsL zO)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decL3_taint : ∃ h, (taint.check (Taint.ofRegs pinned)
    (.seq (.seq (.block (split ++ stealPre)) swap) (.block (argsL tO))) h).isSome = true := ⟨_, by taint_decide⟩

theorem restore_taint : ∃ h, (taint.check (Taint.ofRegs [.r15]) (.block restore) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-! ## The two runs -/

section
variable {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : unitPub s₀ s₀')
include hp hp' hq

theorem tweak_rel (v : UnitImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (tweakTo v.x.enc) fun a b => TwPost s₀ a ∧ TwPost s₀' b := by
  have l := taint_rel [.rsp] ldS_taint (P := fun a b => a = s₀ ∧ b = s₀')
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.mem_singleton] at hr; subst hr; exact pub_rsp hq)
    (F₁ := fun s => s = s₀.setReg .rax (S s₀)) (F₂ := fun s => s = s₀'.setReg .rax (S s₀'))
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨ldS_wp hp, ldS_wp hp'⟩
  have p := taint_rel [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] pro_taint
    (P := fun a b => a = s₀.setReg .rax (S s₀) ∧ b = s₀'.setReg .rax (S s₀'))
    (fun a b h r hr => by
      obtain ⟨rfl, rfl⟩ := h
      have hq' := hq
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_self, pub_S hq]
      all_goals rw [RegUpd.gpr_setReg_of_ne _ _ (by decide), RegUpd.gpr_setReg_of_ne _ _ (by decide)]
      all_goals with_reducible assumption)
    (F₁ := ProPost s₀) (F₂ := ProPost s₀') fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨pro_wp hp, pro_wp hp'⟩
  have c := xcall_rel true v.x.encOk v.x.encCt (n := v.x.enc.name)
    (P := fun a b => ProPost s₀ a ∧ ProPost s₀' b)
    (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
      rw [pub_K hq, pub_Zp hq, pub_Tp hq, pub_S hq, pub_R hq]; exact h.2.pre,
      by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
    (F₁ := TwPost s₀) (F₂ := TwPost s₀')
    (fun a b h => ⟨tcall_wp hp v.x.encOk v.x.encNosp v.x.encDepth h.1,
      tcall_wp hp' v.x.encOk v.x.encNosp v.x.encDepth h.2⟩)
  exact (l.mono (fun _ _ h => h) fun _ _ h => h).seq (p.seq c)

theorem blocksTo_rel (enc : Bool) {n : String} {c : Prog isa}
    (ok : ∀ s, (xtsToX86_64 enc).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (xtsToX86_64 enc).post s s')
    (ct : ConstantTime isa (xtsToX86_64 enc).pre (xtsToX86_64 enc).pub c)
    (nosp : NoSp c) (depth : c.depth ≤ 2) {N N' : Nat} (hN : 16 * N ≤ Len s₀) (hN' : 16 * N' ≤ Len s₀')
    (hNN : N = N') :
    RelCT isa (fun a b => BlocksReady s₀ N a ∧ BlocksReady s₀' N' b) (.call n c)
      fun a b => AllPost enc s₀ N a ∧ AllPost enc s₀' N' b :=
  xtcall_rel enc ok ct
    (fun a b h => ⟨_, _, _, _, _, _, _, h.1.pre, by
      rw [pub_W hq, pub_Tp hq, pub_Sr hq, pub_D hq, pub_S hq, hNN, pub_R hq]; exact h.2.pre,
      by rw [h.1.tw.inv.rsp, h.2.tw.inv.rsp, pub_rsp hq]⟩)
    fun a b h => ⟨blocks_call hp enc ok nosp depth hN h.1.tw h.1.pre,
      blocks_call hp' enc ok nosp depth hN' h.2.tw h.2.pre⟩

theorem restore_rel {enc : Bool} :
    RelCT isa (fun a b => Fin enc s₀ a ∧ Fin enc s₀' b) (.block restore) fun _ _ => True :=
  (taint_rel [.r15] restore_taint (P := fun a b => Fin enc s₀ a ∧ Fin enc s₀' b)
    (fun a b h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h.1.inv.r15, h.2.inv.r15, pub_S hq])
    (F₁ := fun _ => True) (F₂ := fun _ => True)
    fun a b h => ⟨WP.mono (fin_wp hp h.1.inv) fun _ _ => trivial,
      WP.mono (fin_wp hp' h.2.inv) fun _ _ => trivial⟩).mono
    (fun _ _ h => h) fun _ _ _ => trivial

theorem encrypt_rel (v : UnitImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (encryptTo v.x.xts v.xt) fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq v
  have a := taint_rel pinned argsAll_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀)) (F₂ := BlocksReady s₀' (M s₀'))
    fun a b h => ⟨argsAll_wp hp h.1, argsAll_wp hp' h.2⟩
  have c := blocksTo_rel hp hp' hq true v.encToOk v.encToCt v.encToNosp v.encToDepth (by rw [len_eq s₀]; omega_using [])
    (by rw [len_eq s₀']; omega_using []) hM (n := v.encTo.name)
  have cp := taint_rel pinned copyAll_taint
    (P := fun a b => AllPost true s₀ (M s₀) a ∧ AllPost true s₀' (M s₀') b)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := Copied true s₀ (M s₀)) (F₂ := Copied true s₀' (M s₀'))
    fun a b h => ⟨copiedAll_wp hp h.1, copiedAll_wp hp' h.2⟩
  have sp := taint_rel pinned split_taint
    (P := fun a b => Copied true s₀ (M s₀) a ∧ Copied true s₀' (M s₀') b)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := SplitPost true s₀ (M s₀))
    (F₂ := SplitPost true s₀' (M s₀')) fun a b h => ⟨splitCopied_wp hp h.1, splitCopied_wp hp' h.2⟩
  have br : RelCT isa (fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
      (.ite .e (.block []) (encSteal v.x.enc)) fun a b => Fin true s₀ a ∧ Fin true s₀' b := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.zf, h.2.zf, pub_B hq]
    · refine RelCT.block_nil fun a b h => ?_
      have hb : B s₀ = 0 := by
        have := h.2; change a.zf = _ at this; rw [h.1.1.zf] at this; simpa using this
      exact ⟨whole_fin h.1.1.cp hb, whole_fin h.1.2.cp (by rw [← pub_B hq]; exact hb)⟩
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b =>
          SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; change a.zf = _ at this; rw [h.1.1.zf] at this; simpa using this, h.1⟩)
        fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      refine RelCT.assoc (RelCT.assoc ?_)
      have l := taint_rel ([.rax, .r8] ++ pinned) encLast_taint
        (P := fun a b => SplitPost true s₀ (M s₀) a ∧ SplitPost true s₀' (M s₀') b)
        (fun a b h => agree_cons (Inv.agree hq h.1.cp.inv h.2.cp.inv) fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h.1.rax, h.2.rax, hM]
          · rw [h.1.r8, h.2.r8, pub_B hq])
        (F₁ := EncLast s₀) (F₂ := EncLast s₀') fun a b h => ⟨encLast_wp hp h.1 hB, encLast_wp hp' h.2 hB'⟩
      have c := xcall_rel true v.x.encOk v.x.encCt (n := v.x.enc.name)
        (P := fun a b => EncLast s₀ a ∧ EncLast s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Tp hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.pre,
          by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
        (F₁ := Fin true s₀) (F₂ := Fin true s₀')
        fun a b h => ⟨encLastCall_wp hp v h.1 hB, encLastCall_wp hp' v h.2 hB'⟩
      exact l.seq c
  exact t.seq (a.seq (c.seq (cp.seq (sp.seq (br.seq (restore_rel hp hp' hq))))))

theorem decrypt_rel (v : UnitImpl) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (decryptTo v.x.xts v.xt) fun _ _ => True := by
  have hM := pub_M hq
  have t := tweak_rel hp hp' hq v
  have sp := taint_rel pinned split_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
    (fun a b h => Inv.agree hq h.1.inv h.2.inv)
    (F₁ := fun s => TwPost s₀ s ∧ s.zf = some (decide (B s₀ = 0)))
    (F₂ := fun s => TwPost s₀' s ∧ s.zf = some (decide (B s₀' = 0)))
    fun a b h => ⟨split_tw_wp hp h.1, split_tw_wp hp' h.2⟩
  have br : RelCT isa (fun a b => (TwPost s₀ a ∧ a.zf = some (decide (B s₀ = 0))) ∧
      (TwPost s₀' b ∧ b.zf = some (decide (B s₀' = 0))))
      (.ite .e (.seq (.block argsAllTo) (.call v.decTo.name v.decTo.code))
        (.seq (.block argsHeadTo) (.seq (.call v.decTo.name v.decTo.code)
          (.seq (.seq (.block headBytes) copyRest) (decStealTail v.x.dec)))))
      fun a b => Fin false s₀ a ∧ Fin false s₀' b := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.2, h.2.2, pub_B hq]
    · refine (RelCT.exists_ (P := fun (_ : B s₀ = 0) a b => TwPost s₀ a ∧ TwPost s₀' b) fun hb => ?_).mono
        (fun a b h => ⟨by have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hb' : B s₀' = 0 := by rw [← pub_B hq]; exact hb
      have a := taint_rel pinned argsAll_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀))
        (F₂ := BlocksReady s₀' (M s₀')) fun a b h => ⟨argsAll_wp hp h.1, argsAll_wp hp' h.2⟩
      have c := blocksTo_rel hp hp' hq false v.decToOk v.decToCt v.decToNosp v.decToDepth
        (by rw [len_eq s₀]; omega_using []) (by rw [len_eq s₀']; omega_using []) hM (n := v.decTo.name)
      exact a.seq (c.mono (fun _ _ h => h) fun _ _ h => ⟨allPost_fin hp h.1 hb, allPost_fin hp' h.2 hb'⟩)
    · refine (RelCT.exists_ (P := fun (_ : B s₀ ≠ 0) a b => TwPost s₀ a ∧ TwPost s₀' b) fun hB => ?_).mono
        (fun a b h => ⟨by have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this,
          h.1.1.1, h.1.2.1⟩) fun _ _ h => h
      have hB' : B s₀' ≠ 0 := by rw [← pub_B hq]; exact hB
      have a := taint_rel pinned argsHead_taint (P := fun a b => TwPost s₀ a ∧ TwPost s₀' b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := BlocksReady s₀ (M s₀ - 1))
        (F₂ := BlocksReady s₀' (M s₀' - 1)) fun a b h => ⟨argsHead_wp hp h.1, argsHead_wp hp' h.2⟩
      have c₁ := blocksTo_rel hp hp' hq false v.decToOk v.decToCt v.decToNosp v.decToDepth (N := M s₀ - 1)
        (N' := M s₀' - 1) (by rw [len_eq s₀]; omega_using []) (by rw [len_eq s₀']; omega_using []) (by rw [hM])
        (n := v.decTo.name)
      have cp := taint_rel pinned copyHead_taint
        (P := fun a b => AllPost false s₀ (M s₀ - 1) a ∧ AllPost false s₀' (M s₀' - 1) b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := Copied false s₀ (M s₀ - 1))
        (F₂ := Copied false s₀' (M s₀' - 1)) fun a b h => ⟨copiedHead_wp hp h.1, copiedHead_wp hp' h.2⟩
      have l₁ := taint_rel pinned decL1_taint
        (P := fun a b => Copied false s₀ (M s₀ - 1) a ∧ Copied false s₀' (M s₀' - 1) b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL1 s₀) (F₂ := DecL1 s₀')
        fun a b h => ⟨decL1_wp hp h.1, decL1_wp hp' h.2⟩
      have c₂ := xcall_rel false v.x.decOk v.x.decCt (n := v.x.dec.name)
        (P := fun a b => DecL1 s₀ a ∧ DecL1 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Zp hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.pre,
          by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
        (F₁ := DecL2 s₀) (F₂ := DecL2 s₀') fun a b h => ⟨decL2_wp hp v h.1, decL2_wp hp' v h.2⟩
      have l₃ := taint_rel pinned decL3_taint (P := fun a b => DecL2 s₀ a ∧ DecL2 s₀' b)
        (fun a b h => Inv.agree hq h.1.inv h.2.inv) (F₁ := DecL3 s₀) (F₂ := DecL3 s₀')
        fun a b h => ⟨decL3_wp hp h.1 hB, decL3_wp hp' h.2 hB'⟩
      have c₃ := xcall_rel false v.x.decOk v.x.decCt (n := v.x.dec.name)
        (P := fun a b => DecL3 s₀ a ∧ DecL3 s₀' b)
        (fun a b h => ⟨_, _, _, _, _, _, h.1.pre, by
          rw [pub_W hq, pub_Tp hq, pub_L hq, pub_S hq, pub_R hq]; exact h.2.pre,
          by rw [h.1.inv.rsp, h.2.inv.rsp, pub_rsp hq]⟩)
        (F₁ := Fin false s₀) (F₂ := Fin false s₀')
        fun a b h => ⟨decLast_wp hp v h.1 hB, decLast_wp hp' v h.2 hB'⟩
      exact a.seq (c₁.seq (cp.seq (l₁.seq (c₂.seq (RelCT.assoc (RelCT.assoc (l₃.seq c₃)))))))
  exact t.seq (sp.seq (br.seq (restore_rel hp hp' hq)))

end

theorem encrypt_ct (v : UnitImpl) :
    ConstantTime isa (unitToX86_64 true).pre (unitToX86_64 true).pub (encryptTo v.x.xts v.xt) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (encrypt_rel (UPre.of h₁) (UPre.of h₂) hq v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem decrypt_ct (v : UnitImpl) :
    ConstantTime isa (unitToX86_64 false).pre (unitToX86_64 false).pub (decryptTo v.x.xts v.xt) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (decrypt_rel (UPre.of h₁) (UPre.of h₂) hq v _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

theorem encrypt_mx (v : UnitImpl) : (encryptTo v.x.xts v.xt).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [encryptTo, tweakTo, encSteal, swap, copyRest, Code.allInstrs, v.x.encMxcsr, v.encToMxcsr]
  decide +kernel

theorem decrypt_mx (v : UnitImpl) : (decryptTo v.x.xts v.xt).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [decryptTo, tweakTo, decStealTail, swap, copyRest, Code.allInstrs, v.x.encMxcsr, v.x.decMxcsr,
    v.decToMxcsr]
  decide +kernel

theorem encrypt_spSafe (v : UnitImpl) : (encryptTo v.x.xts v.xt).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encryptTo, tweakTo, encSteal, swap, copyRest, Code.all, v.x.encSpSafe, v.encToSpSafe]
  decide +kernel

theorem decrypt_spSafe (v : UnitImpl) : (decryptTo v.x.xts v.xt).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [decryptTo, tweakTo, decStealTail, swap, copyRest, Code.all, v.x.encSpSafe, v.x.decSpSafe,
    v.decToSpSafe]
  decide +kernel

theorem encrypt_correct (v : UnitImpl) (s : State) (hs : (unitToX86_64 true).pre s) :
    ∃ t s', Exec isa (encryptTo v.x.xts v.xt) s t s' ∧ abiPreserved s s' ∧ (unitToX86_64 true).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := encrypt_wp (UPre.of hs) v
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx v) he hg, hp⟩

theorem decrypt_correct (v : UnitImpl) (s : State) (hs : (unitToX86_64 false).pre s) :
    ∃ t s', Exec isa (decryptTo v.x.xts v.xt) s t s' ∧ abiPreserved s s' ∧ (unitToX86_64 false).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := decrypt_wp (UPre.of hs) v
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_mx v) he hg, hp⟩

/-- A state satisfying the precondition: AES-128, a data unit of one block
from `0x4000` to `0x5000` (the first stack argument), and the scratch buffer
at 0 (the third, zero). -/
def unitSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 10 | .rcx => 0x3000 | .r8 => 0x4000 | .r9 => 16
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8009 then 0x50 else if a = 0x8010 then 16 else 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 240⟩, ⟨0x3000, 16⟩, ⟨0x4000, 16⟩, ⟨0x8008, 24⟩]
  wr := [⟨0x5000, 16⟩, ⟨0, 2432⟩]

theorem encrypt_verified (v : UnitImpl) :
    Verified X86_64.target (encryptTo v.x.xts v.xt) (Spec.Xts.aesEncryptUnitToContract X86_64.abi 24) :=
  Verified.of_correct (encrypt_correct v) (encrypt_ct v) (by
    sig_implies [Spec.Xts.aesEncryptUnitToContract, Spec.Xts.aesUnitToSig, Spec.Xts.aesUnitToPre,
      Spec.Xts.aesEncryptUnitToPost, unitToX86_64, unitPre, unitPub, Unit.xtsOf, W, K, R, I, Sr, Len, D, DLen, S,
      schR, tschR, iR, srcR, dstR, scrR, argR, retR, To.stk3, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [unitSat] using unitSat)

theorem decrypt_verified (v : UnitImpl) :
    Verified X86_64.target (decryptTo v.x.xts v.xt) (Spec.Xts.aesDecryptUnitToContract X86_64.abi 24) :=
  Verified.of_correct (decrypt_correct v) (decrypt_ct v) (by
    sig_implies [Spec.Xts.aesDecryptUnitToContract, Spec.Xts.aesUnitToSig, Spec.Xts.aesUnitToPre,
      Spec.Xts.aesDecryptUnitToPost, unitToX86_64, unitPre, unitPub, Unit.xtsOf, W, K, R, I, Sr, Len, D, DLen, S,
      schR, tschR, iR, srcR, dstR, scrR, argR, retR, To.stk3, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr,
      List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs] [unitSat] using unitSat)

/-! ## Instances -/

/-- The whole-block functions of `x`, with its out-of-place ones
(`XtsImpl.to`). -/
def UnitImpl.of (x : Proof.AesXts.X86_64.XtsImpl) : UnitImpl where
  x := x
  encTo := x.to.enc
  encToDepth := x.to.encDepth
  encToOk := x.to.encOk
  encToCt := x.to.encCt
  encToNosp := x.to.encNosp
  encToMxcsr := x.to.encMxcsr
  encToSpSafe := x.to.encSpSafe
  decTo := x.to.dec
  decToDepth := x.to.decDepth
  decToOk := x.to.decOk
  decToCt := x.to.decCt
  decToNosp := x.to.decNosp
  decToMxcsr := x.to.decMxcsr
  decToSpSafe := x.to.decSpSafe

end VG.Proof.AesXts.X86_64.UnitTo

end

end

/-! ### `AesXts.X86_64.Unit.Verified`, which only this module used -/

section

/-!
# XTS-AES of data units on x86-64: `Verified`

Correctness (`encrypt_wp`, `decrypt_wp`) and constant time (`encrypt_ct`,
`decrypt_ct`) for any implementation `v` of the whole-block functions, a
state satisfying the precondition (`unitSat`), and the shared contracts of
`Spec/Xts/Contract.lean`, with 16 bytes of stack: the return addresses of the
call of the whole-block function and of its call of a block function.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Unit

open VG VG.X86_64 VG.Impl.AesXts.X86_64Unit

theorem encrypt_mx (v : XtsImpl) : (encrypt v.xts).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [encrypt, tweak, encSteal, swap, Code.allInstrs, v.encMxcsr]; decide +kernel

theorem decrypt_mx (v : XtsImpl) : (decrypt v.xts).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [decrypt, tweak, decSteal, swap, Code.allInstrs, v.encMxcsr, v.decMxcsr]; decide +kernel

theorem encrypt_spSafe (v : XtsImpl) : (encrypt v.xts).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [encrypt, tweak, encSteal, swap, Code.all, v.encSpSafe]; decide +kernel

theorem decrypt_spSafe (v : XtsImpl) : (decrypt v.xts).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [decrypt, tweak, decSteal, swap, Code.all, v.encSpSafe, v.decSpSafe]; decide +kernel

theorem encrypt_correct (v : XtsImpl) (s : State) (hs : (unitX86_64 true).pre s) :
    ∃ t s', Exec isa (encrypt v.xts) s t s' ∧ abiPreserved s s' ∧ (unitX86_64 true).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := encrypt_wp (UPre.of hs) v
  exact ⟨t, s', he, abiPreserved_of_exec (encrypt_mx v) he hg, hp⟩

theorem decrypt_correct (v : XtsImpl) (s : State) (hs : (unitX86_64 false).pre s) :
    ∃ t s', Exec isa (decrypt v.xts) s t s' ∧ abiPreserved s s' ∧ (unitX86_64 false).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := decrypt_wp (UPre.of hs) v
  exact ⟨t, s', he, abiPreserved_of_exec (decrypt_mx v) he hg, hp⟩

/-- A state satisfying the precondition: AES-128, a data unit of one block
at `0x4000`, and the scratch buffer at 0 (the stack argument, zero). -/
def unitSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 10 | .rcx => 0x3000 | .r8 => 0x4000 | .r9 => 16
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x2000, 240⟩, ⟨0x3000, 16⟩, ⟨0x8008, 8⟩]
  wr := [⟨0x4000, 16⟩, ⟨0, 2432⟩]

theorem encrypt_verified (v : XtsImpl) :
    Verified X86_64.target (encrypt v.xts) (Spec.Xts.aesEncryptUnitContract X86_64.abi 16) :=
  Verified.of_correct (encrypt_correct v) (encrypt_ct v) (by
    sig_implies [Spec.Xts.aesEncryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesEncryptUnitPost, unitX86_64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, argR, retR, stk, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [unitSat] using unitSat)

theorem decrypt_verified (v : XtsImpl) :
    Verified X86_64.target (decrypt v.xts) (Spec.Xts.aesDecryptUnitContract X86_64.abi 16) :=
  Verified.of_correct (decrypt_correct v) (decrypt_ct v) (by
    sig_implies [Spec.Xts.aesDecryptUnitContract, Spec.Xts.aesUnitSig, Spec.Xts.aesUnitPre,
      Spec.Xts.aesDecryptUnitPost, unitX86_64, unitPre, unitPub, xtsOf, W, K, R, I, D, Len, S, schR, tschR, iR,
      dataR, scrR, argR, retR, stk, X86_64.abi, X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range,
      List.range.loop, VG.X86_64.below, X86_64.argRegs] [unitSat] using unitSat)

end VG.Proof.AesXts.X86_64.Unit

end

end


/-!
# XTS-AES of data units on x86-64, without secret residue

`vg_aes_xts_encrypt_unit`, `vg_aes_xts_decrypt_unit` and their out-of-place
counterparts over an implementation of the whole-block functions
(`AesXts.X86_64.XtsImpl`), each followed by `Impl.Scrub.X86_64.scrubTail`
(`X86_64.Scrub.withScrub`) where the implementation gives the residue
analysis of the instance (`XtsImpl.encUnitRes`, …), and otherwise with its
16 or 24 bytes of stack wiped (`X86_64.RScrub.withScrubOrAll`). Their postconditions
read the memory on return only within the buffers (`X86_64.Scrub.PostOut`):
the data, or the output as long as the input, which the out-of-place
functions' precondition requires.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Proof.Aes.X86_64.ModesScrub VG.Proof.Aes.ScrubLocal

/-! ## Postconditions -/

theorem encryptUnitOut (stack : Nat) :
    PostOut (Spec.Xts.aesEncryptUnitContract X86_64.abi stack) (Spec.Xts.aesUnitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Xts.aesUnitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (len_le1 ln)]
      exact h key hk

theorem decryptUnitOut (stack : Nat) :
    PostOut (Spec.Xts.aesDecryptUnitContract X86_64.abi stack) (Spec.Xts.aesUnitSig.retBits 64) :=
  postOut_of_local (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, dt, ln, sc], _ =>
      simp only [Spec.Xts.aesUnitSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.1 (len_le1 ln)]
      exact h key hk

theorem encryptUnitToOut (stack : Nat) :
    PostOut (Spec.Xts.aesEncryptUnitToContract X86_64.abi stack) (Spec.Xts.aesUnitToSig.retBits 64) :=
  postOut_of_local_pre (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, sr, ln, dt, dl, sc], _ =>
      simp only [Spec.Xts.aesUnitToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      have hdl : ((ArgWord.int X86_64.abi.ptrBits).ofRaw dl).toNat = ((ArgWord.int X86_64.abi.ptrBits).ofRaw ln).toNat :=
        hpre.2.2.2
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.2.1 (by rw [← hdl]; exact len_le1 dl)]
      exact h key hk

theorem decryptUnitToOut (stack : Nat) :
    PostOut (Spec.Xts.aesDecryptUnitToContract X86_64.abi stack) (Spec.Xts.aesUnitToSig.retBits 64) :=
  postOut_of_local_pre (leak := none) ScrubAbi.plain fun vs m m₁ m₂ r hlen hpre hb h => by
    match vs, hlen with
    | [sch, tsch, rd, iv, sr, ln, dt, dl, sc], _ =>
      simp only [Spec.Xts.aesUnitToSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq] at hb
      have hdl : ((ArgWord.int X86_64.abi.ptrBits).ofRaw dl).toNat = ((ArgWord.int X86_64.abi.ptrBits).ofRaw ln).toNat :=
        hpre.2.2.2
      show ∀ key, Spec.Xts.KeySchedules m sch tsch _ key → _ = some (Spec.Aes.bytesAt m₂ dt _)
      intro key hk
      rw [bytesAt_of0 hb.2.2.2.2.1 (by rw [← hdl]; exact len_le1 dl)]
      exact h key hk

/-! ## The registrations -/

open VG.X86_64.RScrub VG.Proof.AesXts.X86_64

/-- `Spec.Xts.aesEncryptUnitApi`'s function as emitted over `v` (`Impl.AesXts.X86_64Unit.Fn.encrypt`) meets its contract
in constant time and returns without secret residue: its code is its code
over a stub, with `v`'s where it calls it (`Fill`). -/
theorem encryptUnit_scrubbed (v : XtsImpl) :
    VerifiedScrubbed target (Impl.AesXts.X86_64Unit.Fn.encrypt v.level v.xts) (Spec.Xts.aesEncryptUnitApi.contract X86_64.abi 16) 0 := by
  have := v.encSide
  have := v.decSide
  exact verifiedScrubbedAllFill (api := Spec.Xts.aesEncryptUnitApi) (ks := 0) (n := fun _ => 8)
    (a := Impl.AesXts.X86_64Unit.encrypt ⟨⟨"", .block []⟩, ⟨"", .block []⟩⟩)
    { suffix := v.suffix, code := Impl.AesXts.X86_64Unit.encrypt v.xts, stack := 16, verified := Unit.encrypt_verified v, spSafe := Unit.encrypt_spSafe v }
    v.level (encryptUnitOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Xts.aesDecryptUnitApi`'s function as emitted over `v` (`Impl.AesXts.X86_64Unit.Fn.decrypt`) meets its contract
in constant time and returns without secret residue: its code is its code
over a stub, with `v`'s where it calls it (`Fill`). -/
theorem decryptUnit_scrubbed (v : XtsImpl) :
    VerifiedScrubbed target (Impl.AesXts.X86_64Unit.Fn.decrypt v.level v.xts) (Spec.Xts.aesDecryptUnitApi.contract X86_64.abi 16) 0 := by
  have := v.encSide
  have := v.decSide
  exact verifiedScrubbedAllFill (api := Spec.Xts.aesDecryptUnitApi) (ks := 0) (n := fun _ => 8)
    (a := Impl.AesXts.X86_64Unit.decrypt ⟨⟨"", .block []⟩, ⟨"", .block []⟩⟩)
    { suffix := v.suffix, code := Impl.AesXts.X86_64Unit.decrypt v.xts, stack := 16, verified := Unit.decrypt_verified v, spSafe := Unit.decrypt_spSafe v }
    v.level (decryptUnitOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Xts.aesEncryptUnitToApi`'s function as emitted over `v` (`Impl.AesXts.X86_64UnitTo.Fn.encrypt`), as the
data-unit functions'. -/
theorem encryptUnitTo_scrubbed (v : XtsImpl) :
    VerifiedScrubbed target (Impl.AesXts.X86_64UnitTo.Fn.encrypt v.level v.xts ⟨v.to.enc, v.to.dec⟩)
      (Spec.Xts.aesEncryptUnitToApi.contract X86_64.abi 24) 0 := by
  have := v.encSide
  have := v.decSide
  have := v.toEncSide
  have := v.toDecSide
  exact verifiedScrubbedAllFill (api := Spec.Xts.aesEncryptUnitToApi) (ks := 0) (n := fun s => if s = "to" then 16 else 8)
    (a := Impl.AesXts.X86_64UnitTo.encrypt ⟨⟨"", .block []⟩, ⟨"", .block []⟩⟩ ⟨⟨"to", .block []⟩, ⟨"to", .block []⟩⟩)
    { suffix := v.suffix, code := Impl.AesXts.X86_64UnitTo.encrypt v.xts ⟨v.to.enc, v.to.dec⟩, stack := 24, verified := UnitTo.encrypt_verified (.of v),
      spSafe := UnitTo.encrypt_spSafe (.of v) }
    v.level (encryptUnitToOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)

/-- `Spec.Xts.aesDecryptUnitToApi`'s function as emitted over `v` (`Impl.AesXts.X86_64UnitTo.Fn.decrypt`), as the
data-unit functions'. -/
theorem decryptUnitTo_scrubbed (v : XtsImpl) :
    VerifiedScrubbed target (Impl.AesXts.X86_64UnitTo.Fn.decrypt v.level v.xts ⟨v.to.enc, v.to.dec⟩)
      (Spec.Xts.aesDecryptUnitToApi.contract X86_64.abi 24) 0 := by
  have := v.encSide
  have := v.decSide
  have := v.toEncSide
  have := v.toDecSide
  exact verifiedScrubbedAllFill (api := Spec.Xts.aesDecryptUnitToApi) (ks := 0) (n := fun s => if s = "to" then 16 else 8)
    (a := Impl.AesXts.X86_64UnitTo.decrypt ⟨⟨"", .block []⟩, ⟨"", .block []⟩⟩ ⟨⟨"to", .block []⟩, ⟨"to", .block []⟩⟩)
    { suffix := v.suffix, code := Impl.AesXts.X86_64UnitTo.decrypt v.xts ⟨v.to.enc, v.to.dec⟩, stack := 24, verified := UnitTo.decrypt_verified (.of v),
      spSafe := UnitTo.decrypt_spSafe (.of v) }
    v.level (decryptUnitToOut _) (by fill_calls) (Nat.zero_le _) (Nat.le_refl _)

theorem encryptUnit_spSafeFn (v : XtsImpl) :
    (Impl.AesXts.X86_64Unit.Fn.encrypt v.level v.xts).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Unit.encrypt_spSafe v)

theorem decryptUnit_spSafeFn (v : XtsImpl) :
    (Impl.AesXts.X86_64Unit.Fn.decrypt v.level v.xts).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (Unit.decrypt_spSafe v)

theorem encryptUnitTo_spSafeFn (v : XtsImpl) :
    (Impl.AesXts.X86_64UnitTo.Fn.encrypt v.level v.xts ⟨v.to.enc, v.to.dec⟩).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (UnitTo.encrypt_spSafe (.of v))

theorem decryptUnitTo_spSafeFn (v : XtsImpl) :
    (Impl.AesXts.X86_64UnitTo.Fn.decrypt v.level v.xts ⟨v.to.enc, v.to.dec⟩).all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe (UnitTo.decrypt_spSafe (.of v))

end VG.Proof.AesXts.X86_64.Scrub
