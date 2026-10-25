module

public import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Run
public import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Pre
import VerifiedGarbage.Proof.AesXts.RISCV64.Unit.Steps

/-!
# XTS-AES of data units on PPC64LE: encryption

As on PPC64LE (`Proof/AesXts/PPC64LE/Unit/Enc.lean`). `encrypt_wp`: the
tweak, the call on the whole blocks, and for a partial block the swap and
the call on the last whole block, then the epilogue. The data unit is
`encWith` of the cipher and the tweak, which is `aesXtsEncrypt` of any key
whose schedules are given (`unit_post`).
-/

@[expose] public section

namespace VG.Proof.AesXts.RISCV64.Unit

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.AesXts.RISCV64Unit
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

/-- The memory of `AllPost`. -/
def AllMem (enc : Bool) (s₀ : State) (N : Nat) (m : Mem) : Prop :=
  Spec.Cbc.blocksAt m (D s₀) N = Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (D s₀) N) ∧
    bytesAt m (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N ∧ Frame [⟨D s₀, 16 * N⟩, scrR s₀] s₀.mem m

theorem AllPost.mem {enc : Bool} {s₀ : State} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    AllMem enc s₀ N s.mem :=
  ⟨h.out, h.tw, h.frame⟩

/-- Before a call on the first `N` whole blocks from the tweak. -/
structure BlocksReady (s₀ : State) (N : Nat) (s : State) : Prop where
  tw : TwPost s₀ s
  pre : XPre s (W s₀) (Tp s₀) (D s₀) (Wk s₀) N (R s₀)

/-- Registers other than the ones the invariant needs. -/
theorem keep_of {s s' : State} {P : Reg → Prop} (hg : ∀ r, P r → s'.gpr r = s.gpr r)
    (hP : ∀ r ∈ preserved, r ≠ .s3 → P r) : ∀ r ∈ preserved, r ≠ .s3 → s'.gpr r = s.gpr r :=
  fun r hr h16 => hg r (hP r hr h16)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem AllPost.keep {enc : Bool} {N : Nat} {s s' : State} (h : AllPost enc s₀ N s)
    (hg : ∀ r ∈ preserved, r ≠ .s3 → s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : AllPost enc s₀ N s' where
  inv := Inv.regs hp h.inv hg hsp hm hrd hwr
  out := by rw [hm]; exact h.out
  tw := by rw [hm]; exact h.tw
  frame := by rw [hm]; exact h.frame

/-- After `split`, following the call on the whole blocks. -/
structure SplitPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  all : AllPost enc s₀ N s
  t1 : s.gpr .t1 = BitVec.ofNat 64 (16 * M s₀)
  t2 : s.gpr .t2 = BitVec.ofNat 64 (B s₀)

/-- `s4 + t1 − 16` is the last whole block. -/
theorem last_of {s : State} (h17 : s.gpr .s4 = D s₀) (h10 : s.gpr .t1 = BitVec.ofNat 64 (16 * M s₀)) :
    s.gpr .s4 + s.gpr .t1 - BitVec.ofNat 64 16 = L s₀ := by
  rw [h17, h10, last_eq _ hp.m_pos]

/-- Before the call on the last whole block, from the tweak at offset `o`:
the bytes after the whole blocks swapped with the last whole block's first. -/
structure LastReady (o : Nat) (s₀ s : State) (m : Mem) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (S s₀ + BitVec.ofNat 64 o) (L s₀) (Wk s₀) 1 (R s₀)
  mem : s.mem = swapMem m (L s₀) (B s₀)

/-- The swap, and the arguments of the call on the last whole block. -/
theorem steal_wp {o : Nat} (ho : o = tO ∨ o = zO) {s : State} (hi : Inv s₀ s)
    (h10 : s.gpr .t1 = BitVec.ofNat 64 (16 * M s₀)) (h11 : s.gpr .t2 = BitVec.ofNat 64 (B s₀))
    (h12 : s.gpr .t3 = L s₀) (hB : B s₀ ≠ 0) :
    WP isa (.seq swap (.block (argsL o))) s fun s' => LastReady o s₀ s' s.mem := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  have wr' : s.wr = [dataR s₀, scrR s₀] := by rw [hi.wr, hp.wr]
  refine WP.seq (WP.mono (swap_wp s (Nat.pos_of_ne_zero hB) hb h12 h11 (fun i hi' => by
      rw [wr']
      exact in_rw (r := dataR s₀) (by simp)
        (hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega) (by omega)))))
    fun s₂ ⟨mem₂, g₂, rd₂, wr₂, sp₂⟩ => ?_)
  refine WP.mono (argsL_wp' s₂ (o := o) (by rcases ho with rfl | rfl <;> decide))
    fun s₃ ⟨a0₃, a1₃, a2₃, a3₃, a4₃, a5₃, cs₃, mem₃, rd₃, wr₃, sp₃⟩ => ?_
  have k₂ (r : Reg) (hr : r ∈ preserved) : s₂.gpr r = s.gpr r :=
    g₂ r (pres_ne hr (by decide)) (pres_ne hr (by decide)) (pres_ne hr (by decide)) (pres_ne hr (by decide))
  have inv₂ : Inv s₀ s₂ := Inv.step hp hi (rs := [⟨L s₀, 16 + B s₀⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, hp.lb_sub⟩)
    (by rw [mem₂]; exact Proof.AesXts.Unit.swapMem_frame _ _ _) (fun r hr _ => k₂ r hr) sp₂ rd₂ wr₂
  have inv₃ : Inv s₀ s₃ := Inv.regs hp inv₂ (fun r hr _ => cs₃ r hr) sp₃ mem₃ rd₃ wr₃
  refine ⟨inv₃, xpre_last hp inv₃.rd inv₃.wr ho (by rw [a0₃, inv₂.s1])
    (by rw [a1₃, inv₂.s2, a2_ofNat]) (by rw [a2₃, inv₂.s6]) ?_ a4₃ (by rw [a5₃, inv₂.s6]),
    by rw [mem₃, mem₂]⟩
  rw [a3₃, g₂ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide)
    (by decide)]
  exact last_of hp hi.s4 h10

/-- The call on the last whole block, and the data unit's ciphertext. -/
theorem encLastCall_wp (ok : XtsOk true Impl.AesXts.RISCV64.encrypt)
    (nf : Impl.AesXts.RISCV64.encrypt.noFrames = true)
    {s : State} {m : Mem} (h : LastReady tO s₀ s m) (hm : AllMem true s₀ (M s₀) m) (hB : B s₀ ≠ 0) :
    WP isa encCall s (Fin true s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨hout, htw, hfr⟩ := hm
  refine WP.mono (xts_call true ok nf h.pre) fun s₄ c => ?_
  have sw := Proof.AesXts.Unit.swapMem_frame m (L s₀) (B s₀)
  refine ⟨Inv.call hp h.inv t_sub (.inl hp.l_sub) c, ?_⟩
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.enc_steal hp.m_pos (Nat.pos_of_ne_zero hB) hb hout ?_ ⟨?_, ?_, ?_⟩
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.tl_blocks
      · exact hp.data_scr.sub_left hp.tl_sub) (by omega)
  · rw [Proof.AesXts.Unit.crypt_one_of c.out,
      hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl <;> simp), h.mem,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left (sub_trans t_sub tz_sub)).sub_right hp.lb_sub) (by decide), htw]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega)) hp.hd_l
      (sub_trans t_sub tz_sub) c (by dsimp only; have := hp.wrapD; omega), h.mem]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l (sub_trans t_sub tz_sub) c
      (by dsimp only; omega), h.mem]

/-- The last whole block's address, after `split`. -/
theorem lastAddr_wp {s : State} (hi : Inv s₀ s) (h10 : s.gpr .t1 = BitVec.ofNat 64 (16 * M s₀)) :
    WP isa (.block lastAddr) s fun s' => s'.gpr .t3 = L s₀ ∧ (∀ r, r ≠ .t3 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (lastAddr_wp' s) fun _ ⟨t3, g, mem, rd, wr, sp⟩ =>
    ⟨by rw [t3]; exact last_of hp hi.s4 h10, g, sp, mem, rd, wr⟩

omit hp in
theorem keep_t3 {s s' : State} (hg : ∀ r, r ≠ .t3 → s'.gpr r = s.gpr r) :
    ∀ r ∈ preserved, r ≠ .s3 → s'.gpr r = s.gpr r :=
  fun r hr _ => hg r (pres_ne hr (by decide))

/-- Before the call on the last whole block of encryption: `Cₘ` and `PP`
swapped into place. -/
def EncLast (s₀ s : State) : Prop := ∃ m, AllMem true s₀ (M s₀) m ∧ LastReady tO s₀ s m

theorem encLast_wp {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block lastAddr) swap) (.block (argsL tO))) s (EncLast s₀) := by
  refine WP.assoc' (WP.seq (WP.mono (lastAddr_wp hp h.all.inv h.t1) fun s₁ ⟨t3₁, g₁, sp₁, mem₁, rd₁, wr₁⟩ => ?_))
  have h₁ := AllPost.keep hp h.all (keep_t3 g₁) sp₁ mem₁ rd₁ wr₁
  exact WP.mono (steal_wp hp (.inl rfl) h₁.inv (by rw [g₁ _ (by decide), h.t1])
    (by rw [g₁ _ (by decide), h.t2]) t3₁ hB) fun _ h₂ => ⟨_, h₁.mem, h₂⟩

/-- The steal of encryption: `Cₘ` and `PP` swapped into place, and `PP`
enciphered with the tweak of block `M`. -/
theorem encSteal_wp (ok : XtsOk true Impl.AesXts.RISCV64.encrypt)
    (nf : Impl.AesXts.RISCV64.encrypt.noFrames = true)
    {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa encSteal s (Fin true s₀) :=
  WP.assoc (WP.assoc (WP.seq (WP.mono (encLast_wp hp h hB) fun _ ⟨_, hm, h'⟩ =>
    encLastCall_wp hp ok nf h' hm hB)))

/-- The postcondition, from the bytes of the data unit. -/
theorem unit_post {enc : Bool} {s' : State}
    (hd : bytesAt s'.mem (D s₀) (Len s₀) = withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (D s₀) (Len s₀))) :
    (unitRISCV64 enc).post s₀ s' := by
  intro key hk
  have hk' := Proof.AesXts.Unit.keys_of (bytesAt s₀.mem (I s₀) 16) hk
  have hl : 16 ≤ (bytesAt s₀.mem (D s₀) (Len s₀)).length := by
    rw [Proof.AesXts.Unit.length_bytesAt]; exact hp.len_lo
  cases enc
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsDecrypt_eq hk' hl, hd]; rfl
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsEncrypt_eq hk' hl, hd]; rfl

omit hp in
/-- After `split`: the bytes of the whole blocks in `t1`, and the bytes
after them in `t2`. -/
theorem split_wp {s : State} (h : Inv s₀ s) :
    WP isa (.block split) s fun s' => s'.gpr .t1 = BitVec.ofNat 64 (16 * M s₀) ∧
      s'.gpr .t2 = BitVec.ofNat 64 (B s₀) ∧ (∀ r, r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  WP.mono (split_wp' s) fun _ ⟨t1, t2, g, mem, rd, wr, sp⟩ =>
    ⟨by rw [t1, h.s5], by rw [t2, h.s5], g, sp, mem, rd, wr⟩

omit hp in
theorem keep_t1t2 {s s' : State} (hg : ∀ r, r ≠ .t1 → r ≠ .t2 → s'.gpr r = s.gpr r) :
    ∀ r ∈ preserved, r ≠ .s3 → s'.gpr r = s.gpr r :=
  fun r hr _ => hg r (pres_ne hr (by decide)) (pres_ne hr (by decide))

/-- The arguments of the call on the whole blocks. -/
theorem argsAll_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsAll) s (BlocksReady s₀ (M s₀)) :=
  WP.mono (argsAll_wp' s) fun s₂ ⟨r3₂, r4₂, r5₂, r6₂, r7₂, r8₂, cs₂, mem₂, rd₂, wr₂, sp₂⟩ =>
    have h₂ := TwPost.keep hp h cs₂ sp₂ mem₂ rd₂ wr₂
    ⟨h₂, xpre_blocks hp h₂.inv.rd h₂.inv.wr (N := M s₀)
      (by rw [len_eq s₀]; omega) (by rw [r3₂, h.inv.s1]) (by rw [r4₂, h.inv.s2, a2_ofNat])
      (by rw [r5₂, h.inv.s6]) (by rw [r6₂, h.inv.s4]) (by rw [r7₂, h.inv.s5]) (by rw [r8₂, h.inv.s6])⟩

theorem splitAll_wp {enc : Bool} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    WP isa (.block split) s (SplitPost enc s₀ N) :=
  WP.mono (split_wp h.inv) fun _ ⟨t1, t2, g, sp, mem, rd, wr⟩ =>
    ⟨AllPost.keep hp h (keep_t1t2 g) sp mem rd wr, t1, t2⟩

omit hp in
/-- The data unit of whole blocks, after the call on all of them. -/
theorem whole_fin {enc : Bool} {s : State} (h : AllPost enc s₀ (M s₀) s) (hb : B s₀ = 0) : Fin enc s₀ s := by
  refine ⟨h.inv, ?_⟩
  rw [show Len s₀ = 16 * M s₀ by rw [len_eq s₀, hb, Nat.add_zero]]
  cases enc
  · exact Proof.AesXts.Unit.dec_whole h.out
  · exact Proof.AesXts.Unit.enc_whole h.out

omit hp in
theorem eval_b {s : State} (h : s.gpr .t2 = BitVec.ofNat 64 (B s₀)) :
    isa.eval (.zero .t2) s = some (decide (B s₀ = 0)) :=
  eval_zero_ofNat s .t2 (by have : B s₀ < 16 := Nat.mod_lt _ (by decide); omega) h

theorem encrypt_wp (ok : XtsOk true Impl.AesXts.RISCV64.encrypt)
    (nf : Impl.AesXts.RISCV64.encrypt.noFrames = true) :
    WP isa Impl.AesXts.RISCV64Unit.encrypt s₀ fun s' => Restored s₀ s' ∧ (unitRISCV64 true).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp ok nf) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (argsAll_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (blocks_call hp true ok nf (by rw [len_eq s₀]; omega) h₂.tw h₂.pre) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (splitAll_wp hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b h₄.t2)
    (fun hb => WP.block_nil (whole_fin h₄.all (by simpa using hb)))
    (fun hb => encSteal_wp hp ok nf h₄ (by simpa using hb))) fun s₅ h₅ => ?_)
  exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m, _⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.RISCV64.Unit
