module

public import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Run
public import VerifiedGarbage.Proof.AesXts.Unit
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Steps
import VerifiedGarbage.Proof.AesXts.AArch64.Unit.Pre
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.AesCbc.AArch64.Loop

/-!
# XTS-AES of data units on AArch64: encryption

`encrypt_wp`: the tweak, the call on the whole blocks, and for a partial
block the swap and the call on the last whole block, then the epilogue,
for any implementation `f` of the whole-block encryption. The data unit is
`encWith` of the cipher and the tweak, which is `aesXtsEncrypt` of any key
whose schedules are given (`unit_post`).
-/

@[expose] public section

namespace VG.Proof.AesXts.AArch64.Unit

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesXts.AArch64Unit
open VG.Proof.AesCbc.AArch64 (modeAArch64)
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
  pre : XPre s (W s₀) (Tp s₀) (D s₀) (S s₀) N (R s₀)

/-- A whole-block function, verified. -/
abbrev XtsOk (enc : Bool) (c : Prog isa) : Prop :=
  ∀ s, (modeAArch64 (AesXts.xtsMode enc)).pre s →
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (modeAArch64 (AesXts.xtsMode enc)).post s s'

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem AllPost.keep {enc : Bool} {N : Nat} {s s' : State} (h : AllPost enc s₀ N s)
    (hg : ∀ r ∈ pinned, s'.gpr r = s.gpr r) (hsp : s'.sp = s.sp)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : AllPost enc s₀ N s' where
  inv := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _) hg hsp hrd hwr
  out := by rw [hm]; exact h.out
  tw := by rw [hm]; exact h.tw
  frame := by rw [hm]; exact h.frame

/-- After `split`, following the call on the whole blocks. -/
structure SplitPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  all : AllPost enc s₀ N s
  x9 : s.gpr .x9 = BitVec.ofNat 64 (16 * M s₀)
  x10 : s.gpr .x10 = BitVec.ofNat 64 (B s₀)

/-- `x23 + x9 − 16` is the last whole block. -/
theorem last_of {s : State} (h23 : s.gpr .x23 = D s₀) (h9 : s.gpr .x9 = BitVec.ofNat 64 (16 * M s₀)) :
    s.gpr .x23 + s.gpr .x9 - BitVec.ofNat 64 16 = L s₀ := by
  rw [h23, h9, last_eq _ hp.m_pos]

/-- Before the call on the last whole block, from the tweak at offset `o`:
the bytes after the whole blocks swapped with the last whole block's first. -/
structure LastReady (o : Nat) (s₀ s : State) (m : Mem) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (S s₀ + BitVec.ofNat 64 o) (L s₀) (S s₀) 1 (R s₀)
  mem : s.mem = swapMem m (L s₀) (B s₀)

/-- The swap, and the arguments of the call on the last whole block. -/
theorem steal_wp {o : Nat} (ho : o = tO ∨ o = zO) {s : State} (hi : Inv s₀ s)
    (h9 : s.gpr .x9 = BitVec.ofNat 64 (16 * M s₀)) (h10 : s.gpr .x10 = BitVec.ofNat 64 (B s₀))
    (h11 : s.gpr .x11 = L s₀) (hB : B s₀ ≠ 0) :
    WP isa (.seq swap (.block (argsL o))) s fun s' => LastReady o s₀ s' s.mem := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  have wr' : s.wr = [dataR s₀, scrR s₀] := by rw [hi.wr, hp.wr]
  refine WP.seq (WP.mono (swap_ok s (Nat.pos_of_ne_zero hB) hb h11 h10 (fun i hi' => by
      rw [wr']
      exact in_rw (r := dataR s₀) (by simp)
        (hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega) (by omega)))))
    fun s₂ ⟨mem₂, g₂, sp₂, rd₂, wr₂⟩ => ?_)
  obtain ⟨s₃, run₃, x0₃, x1₃, x2₃, x3₃, x4₃, x5₃, cs₃, sp₃, mem₃, rd₃, wr₃⟩ :=
    argsL_ok s₂ (o := o) (by rcases ho with rfl | rfl <;> decide)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have k₂ (r : Reg) (hr : r ∈ pinned) : s₂.gpr r = s.gpr r := by
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact g₂ _ (by decide) (by decide) (by decide) (by decide)
  have inv₂ : Inv s₀ s₂ := Inv.step hp hi (rs := [⟨L s₀, 16 + B s₀⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl hp.lb_sub)
    (by rw [mem₂]; exact Proof.AesXts.Unit.swapMem_frame _ _ _) k₂ sp₂ rd₂ wr₂
  have inv₃ : Inv s₀ s₃ := Inv.step hp inv₂ (rs := []) (fun _ h => by simp at h)
    (by rw [mem₃]; exact Frame.refl _ _) (fun r hr => cs₃ r (pinned_pres r hr).1) sp₃ rd₃ wr₃
  refine ⟨inv₃, xpre_last hp inv₃.rd inv₃.wr ho (by rw [x0₃, inv₂.x19])
    (by rw [x1₃, inv₂.x20, x1_ofNat]) (by rw [x2₃, inv₂.x24]) ?_ x4₃ (by rw [x5₃, inv₂.x24]), by rw [mem₃, mem₂]⟩
  rw [x3₃, g₂ _ (by decide) (by decide) (by decide) (by decide), g₂ _ (by decide) (by decide) (by decide)
    (by decide)]
  exact last_of hp hi.x23 h9

/-- The call on the last whole block, and the data unit's ciphertext. -/
theorem encLastCall_wp {f : Impl.Aes.AArch64.Blocks} (ok : XtsOk true f.code) (nf : f.code.noFrames = true)
    {s : State} {m : Mem} (h : LastReady tO s₀ s m) (hm : AllMem true s₀ (M s₀) m) (hB : B s₀ ≠ 0) :
    WP isa (.call f.name f.code) s (Fin true s₀) := by
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
        exact (hp.data_scr.symm.sub_left (sub_trans t_sub s_sub)).sub_right hp.lb_sub) (by decide), htw]
  · rw [call_keeps hp (X := ⟨D s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega)) hp.hd_l
      (sub_trans t_sub s_sub) c (by dsimp only; have := hp.wrapD; omega), h.mem]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega)
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub tl_l (sub_trans t_sub s_sub) c
      (by dsimp only; omega), h.mem]

/-- The last whole block's address, after `split`. -/
theorem lastAddr_wp {s : State} (hi : Inv s₀ s) (h9 : s.gpr .x9 = BitVec.ofNat 64 (16 * M s₀)) {Q : State → Prop}
    (hq : ∀ s', s'.gpr .x11 = L s₀ → (∀ r, r ≠ .x11 → s'.gpr r = s.gpr r) → s'.sp = s.sp → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block lastAddr) s Q := by
  obtain ⟨s', run', x11', g', sp', mem', rd', wr'⟩ := lastAddr_ok s
  exact WP.of_runBlock ⟨s', run', hq s' (by rw [x11']; exact last_of hp hi.x23 h9) g' sp' mem' rd' wr'⟩

omit hp in
theorem keep_x11 {s s' : State} (hg : ∀ r, r ≠ .x11 → s'.gpr r = s.gpr r) : ∀ r ∈ pinned, s'.gpr r = s.gpr r :=
  fun r hr => hg r (by
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

/-- Before the call on the last whole block of encryption: `Cₘ` and `PP`
swapped into place. -/
def EncLast (s₀ s : State) : Prop := ∃ m, AllMem true s₀ (M s₀) m ∧ LastReady tO s₀ s m

theorem encLast_wp {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (.seq (.seq (.block lastAddr) swap) (.block (argsL tO))) s (EncLast s₀) := by
  refine WP.assoc' (WP.seq (lastAddr_wp hp h.all.inv h.x9 fun s₁ x11₁ g₁ sp₁ mem₁ rd₁ wr₁ => ?_))
  have h₁ := AllPost.keep hp h.all (keep_x11 g₁) sp₁ mem₁ rd₁ wr₁
  exact WP.mono (steal_wp hp (.inl rfl) h₁.inv (by rw [g₁ _ (by decide), h.x9])
    (by rw [g₁ _ (by decide), h.x10]) x11₁ hB) fun _ h₂ => ⟨_, h₁.mem, h₂⟩

/-- The steal of encryption: `Cₘ` and `PP` swapped into place, and `PP`
enciphered with the tweak of block `M`. -/
theorem encSteal_wp {f : Impl.Aes.AArch64.Blocks} (ok : XtsOk true f.code) (nf : f.code.noFrames = true)
    {s : State} (h : SplitPost true s₀ (M s₀) s) (hB : B s₀ ≠ 0) :
    WP isa (encSteal f) s (Fin true s₀) :=
  WP.assoc (WP.assoc (WP.seq (WP.mono (encLast_wp hp h hB) fun _ ⟨_, hm, h'⟩ =>
    encLastCall_wp hp ok nf h' hm hB)))

/-- The postcondition, from the bytes of the data unit. -/
theorem unit_post {enc : Bool} {s' : State}
    (hd : bytesAt s'.mem (D s₀) (Len s₀) = withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (D s₀) (Len s₀))) :
    (unitAArch64 enc).post s₀ s' := by
  intro key hk
  have hk' := Proof.AesXts.Unit.keys_of (bytesAt s₀.mem (I s₀) 16) hk
  have hl : 16 ≤ (bytesAt s₀.mem (D s₀) (Len s₀)).length := by
    rw [Proof.AesXts.Unit.length_bytesAt]; exact hp.len_lo
  cases enc
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsDecrypt_eq hk' hl, hd]; rfl
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsEncrypt_eq hk' hl, hd]; rfl

omit hp in
/-- After `split`: the bytes of the whole blocks in `x9`, and the bytes
after them in `x10`. -/
theorem split_wp {s : State} (h : Inv s₀ s) {Q : State → Prop}
    (hq : ∀ s', s'.gpr .x9 = BitVec.ofNat 64 (16 * M s₀) → s'.gpr .x10 = BitVec.ofNat 64 (B s₀) →
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) → s'.sp = s.sp → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → Q s') :
    WP isa (.block split) s Q := by
  obtain ⟨s', run', x9', x10', g', sp', mem', rd', wr'⟩ := split_ok s
  rw [h.x22] at x9' x10'
  exact WP.of_runBlock ⟨s', run', hq s' x9' x10' g' sp' mem' rd' wr'⟩

omit hp in
theorem keep_x9x10 {s s' : State} (hg : ∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) :
    ∀ r ∈ pinned, s'.gpr r = s.gpr r :=
  fun r hr => by
    simp only [pinned, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)

/-- The arguments of the call on the whole blocks. -/
theorem argsAll_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsAll) s (BlocksReady s₀ (M s₀)) := by
  obtain ⟨s₂, run₂, x0₂, x1₂, x2₂, x3₂, x4₂, x5₂, cs₂, sp₂, mem₂, rd₂, wr₂⟩ := argsAll_ok s
  have h₂ := TwPost.keep hp h cs₂ sp₂ mem₂ rd₂ wr₂
  exact WP.of_runBlock ⟨s₂, run₂, h₂, xpre_blocks hp h₂.inv.rd h₂.inv.wr (N := M s₀)
    (by rw [len_eq s₀]; omega) (by rw [x0₂, h.inv.x19]) (by rw [x1₂, h.inv.x20, x1_ofNat])
    (by rw [x2₂, h.inv.x24]) (by rw [x3₂, h.inv.x23]) (by rw [x4₂, h.inv.x22]) (by rw [x5₂, h.inv.x24])⟩

theorem splitAll_wp {enc : Bool} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    WP isa (.block split) s (SplitPost enc s₀ N) :=
  split_wp h.inv fun _ x9₄ x10₄ g₄ sp₄ mem₄ rd₄ wr₄ =>
    ⟨AllPost.keep hp h (keep_x9x10 g₄) sp₄ mem₄ rd₄ wr₄, x9₄, x10₄⟩

omit hp in
/-- The data unit of whole blocks, after the call on all of them. -/
theorem whole_fin {enc : Bool} {s : State} (h : AllPost enc s₀ (M s₀) s) (hb : B s₀ = 0) : Fin enc s₀ s := by
  refine ⟨h.inv, ?_⟩
  rw [show Len s₀ = 16 * M s₀ by rw [len_eq s₀, hb, Nat.add_zero]]
  cases enc
  · exact Proof.AesXts.Unit.dec_whole h.out
  · exact Proof.AesXts.Unit.enc_whole h.out

omit hp in
theorem eval_b {s : State} (h : s.gpr .x10 = BitVec.ofNat 64 (B s₀)) :
    isa.eval (.zero .x .x10) s = some (decide (B s₀ = 0)) :=
  eval_z h (by have : B s₀ < 16 := Nat.mod_lt _ (by decide); omega)

theorem encrypt_wp {f : Impl.Aes.AArch64.Blocks} (ok : XtsOk true f.code) (nf : f.code.noFrames = true) :
    WP isa (Impl.AesXts.AArch64Unit.encrypt f) s₀ fun s' => GprAbi s₀ s' ∧ (unitAArch64 true).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp ok nf) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (argsAll_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (blocks_call hp true ok nf (by rw [len_eq s₀]; omega) h₂.tw h₂.pre) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (splitAll_wp hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b h₄.x10)
    (fun hb => WP.block_nil (whole_fin h₄.all (by simpa using hb)))
    (fun hb => encSteal_wp hp ok nf h₄ (by simpa using hb))) fun s₅ h₅ => ?_)
  exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.AArch64.Unit
