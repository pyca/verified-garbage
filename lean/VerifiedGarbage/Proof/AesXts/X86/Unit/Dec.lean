module

public import VerifiedGarbage.Proof.AesXts.X86.Unit.Run
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset

/-! ### `AesXts.X86.Unit.Enc`, which only this module used -/

section

/-!
# XTS-AES of data units on x86: encryption

`encrypt_wp`: the tweak, the call on the whole blocks, and for a partial
block the swap and the call on the last whole block (`steal_wp`, which
decryption ends with too), then the epilogue. The data unit is `encWith` of
the cipher and the tweak, which is `aesXtsEncrypt` of any key whose
schedules are given (`unit_post`).
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.Unit

open VG VG.X86 VG.Impl.AesXts.X86Unit
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

/-- The data unit's result in a direction. -/
def withOf : Bool → Spec.Cbc.Cipher → List Byte → List Byte → List Byte
  | true => encWith
  | false => decWith

/-- What each branch leaves before the epilogue. -/
structure Fin (enc : Bool) (s₀ s : State) : Prop where
  inv : Inv s₀ s
  data : bytesAt s.mem (Da s₀) (Len s₀) =
    withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (Da s₀) (Len s₀))

/-- The memory of `AllPost`. -/
def AllMem (enc : Bool) (s₀ : State) (N : Nat) (m : Mem) : Prop :=
  Spec.Cbc.blocksAt m (Da s₀) N = Spec.Xts.crypt (ciph s₀ enc) (t0 s₀) (Spec.Cbc.blocksAt s₀.mem (Da s₀) N) ∧
    bytesAt m (Tp s₀) 16 = Spec.Xts.next (t0 s₀) N ∧ Frame [⟨Da s₀, 16 * N⟩, scrR s₀, stkR s₀] s₀.mem m

theorem AllPost.mem {enc : Bool} {s₀ : State} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    AllMem enc s₀ N s.mem :=
  ⟨h.out, h.tw, h.frame⟩

/-- Before a call on the first `N` whole blocks from the tweak. -/
structure BlocksReady (s₀ : State) (N : Nat) (s : State) : Prop where
  tw : TwPost s₀ s
  pre : XPre s (W s₀) (Tv s₀) (D s₀) (S s₀) N (R s₀)

/-- After `split`, following the call on the whole blocks. -/
structure SplitPost (enc : Bool) (s₀ : State) (N : Nat) (s : State) : Prop where
  all : AllPost enc s₀ N s
  esi : s.gpr .esi = BitVec.ofNat 32 (B s₀)
  zf : s.zf = some (decide (B s₀ = 0))

/-- Before the call on the last whole block, from the tweak at offset `o`:
the bytes after the whole blocks swapped with the last whole block's first. -/
structure LastReady (o : Nat) (s₀ s : State) (m : Mem) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (S s₀ + BitVec.ofNat 32 o) (Lv s₀) (S s₀) 1 (R s₀)
  mem : s.mem = swapMem m (L s₀) (B s₀)

/-- A block, as itself followed by nothing. -/
theorem blk {l : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block (l ++ [])) s Q) :
    WP isa (.block l) s Q := by
  rwa [List.append_nil] at h

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem AllPost.keep {enc : Bool} {N : Nat} {s s' : State} (h : AllPost enc s₀ N s)
    (hesp : s'.gpr .esp = s.gpr .esp) (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    AllPost enc s₀ N s' where
  inv := Inv.step hp h.inv (rs := []) (fun _ h => by simp at h) (by rw [hm]; exact Frame.refl _ _) hesp hrd hwr
  out := by rw [hm]; exact h.out
  tw := by rw [hm]; exact h.tw
  frame := by rw [hm]; exact h.frame

theorem UPre.l_fit : (Lv s₀).toNat + 16 + B s₀ ≤ 2 ^ 32 := by
  have := hp.data_fit; have := len_eq s₀; have := hp.m_pos
  rw [hp.dataN (by omega_arith)]
  omega_arith

theorem UPre.lb_in {s : State} (hwr : s.wr = s₀.wr) (i : Nat) (hi : i < 16 + B s₀) :
    InRegions s.wr (L s₀ + BitVec.ofNat 64 i) 1 := by
  have : B s₀ < 16 := Nat.mod_lt _ (by decide)
  rw [hwr, hp.wr]
  exact ⟨dataR s₀, by simp,
    hp.lb_sub _ (Offset.contains_base (L s₀) (d := i) (n := 1) (k := 16 + B s₀) (by omega_using [hi]) (by omega_using [hi, this]))⟩

/-- The code of the steal before its call. -/
abbrev stealPre : Prog isa := .seq (.seq (.block lastAddr) swap) (.block (argsL tO))

/-- The steal before its call: the last whole block's address, the swap, and
the arguments of the call on the last whole block from the tweak. -/
theorem stealPre_wp {s : State} (hi : Inv s₀ s) (hsi : s.gpr .esi = BitVec.ofNat 32 (B s₀)) (hB : B s₀ ≠ 0) :
    WP isa stealPre s fun s' => LastReady tO s₀ s' s.mem := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  refine WP.seq (WP.seq (WP.mono (blk (lastAddr_wp (Inv.args hp hi) hp hsi fun s₁ c₁ dx cx => WP.block_nil
    (M := isa) (Q := fun (s₁ : State) => Inv s₀ s₁ ∧ s₁.mem = s.mem ∧ s₁.gpr .esi = BitVec.ofNat 32 (B s₀) ∧
      s₁.gpr .edx = Lv s₀ ∧ s₁.gpr .ecx = BitVec.ofNat 32 (B s₀))
    ⟨Inv.step hp hi (rs := []) (fun _ h => by simp at h) (by rw [c₁.mem]; exact Frame.refl _ _)
      (c₁.gpr _ (by decide)) c₁.rd c₁.wr, c₁.mem, by rw [c₁.gpr _ (by decide), hsi], dx, cx⟩)) fun s₁ h₁ => ?_))
  obtain ⟨i₁, m₁, si₁, dx₁, cx₁⟩ := h₁
  refine WP.mono (swap_ok s₁ (Nat.pos_of_ne_zero hB) hb (by rw [dx₁]; exact hp.lA)
      (by rw [dx₁]; exact hp.l_fit) cx₁ (hp.lb_in i₁.wr)) fun s₂ c₂ => ?_
  have inv₂ : Inv s₀ s₂ := Inv.step hp i₁ (rs := [⟨L s₀, 16 + B s₀⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inl hp.lb_sub)
    (by rw [c₂.mem]; exact Proof.AesXts.Unit.swapMem_frame _ _ _) (c₂.gpr _ (by decide)) c₂.rd c₂.wr
  have si₂ : s₂.gpr .esi = BitVec.ofNat 32 (B s₀) := by rw [c₂.gpr _ (by decide), si₁]
  refine blk (argsL_wp (o := tO) (Inv.args hp inv₂) hp si₂ fun s₃ c₃ ax cx dx bx di bp =>
    WP.block_nil (M := isa) (Q := fun (s₃ : State) => LastReady tO s₀ s₃ s.mem) ?_)
  have inv₃ : Inv s₀ s₃ := Inv.step hp inv₂ (rs := []) (fun _ h => by simp at h)
    (by rw [c₃.mem]; exact Frame.refl _ _) (c₃.gpr _ (by decide)) c₃.rd c₃.wr
  exact ⟨inv₃, xpre_last hp inv₃.rd inv₃.wr inv₃.esp (.inl rfl) ax (by rw [cx, r_ofNat]) dx bx di bp,
    by rw [c₃.mem, c₂.mem, m₁]⟩

/-- The steal: `stealPre` and the call on the last whole block. -/
theorem steal_wp {f : Impl.Aes.X86.Blocks} {s : State} {Q : State → Prop} (hi : Inv s₀ s)
    (hsi : s.gpr .esi = BitVec.ofNat 32 (B s₀)) (hB : B s₀ ≠ 0)
    (k : ∀ s', LastReady tO s₀ s' s.mem → WP isa (xcall f) s' Q) : WP isa (encSteal f) s Q :=
  WP.assoc (WP.assoc (WP.seq (WP.mono (stealPre_wp hp hi hsi hB) k)))

/-- The call on the last whole block, and the data unit's ciphertext. -/
theorem encLastCall_wp {f : Impl.Aes.X86.Blocks} (hf : XFn true f) {s : State} {m : Mem}
    (h : LastReady tO s₀ s m) (hm : AllMem true s₀ (M s₀) m) (hB : B s₀ ≠ 0) :
    WP isa (xcall f) s (Fin true s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨hout, htw, hfr⟩ := hm
  have aT := hp.scrW (d := tO) (by decide)
  have aL := hp.lA
  refine WP.mono (xts_call true hf.ok hf.nosp hf.stack h.pre) fun s₄ c => ?_
  have sw := Proof.AesXts.Unit.swapMem_frame m (L s₀) (B s₀)
  have tS : Region.Sub ⟨(S s₀ + BitVec.ofNat 32 tO).setWidth 64, 16⟩ (scrR s₀) := by
    rw [aT]; exact sub_trans t_sub s_sub
  refine ⟨Inv.call hp h.inv (by rw [aT]; exact t_sub) (.inl (by rw [aL]; exact hp.l_sub)) c, ?_⟩
  rw [len_eq s₀]
  refine Proof.AesXts.Unit.enc_steal hp.m_pos (Nat.pos_of_ne_zero hB) hb hout ?_ ⟨?_, ?_, ?_⟩
  · exact Proof.Cmac.bytesAt_frame hfr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.tl_blocks
      · exact hp.data_scr.sub_left hp.tl_sub
      · exact hp.stk_data.symm.sub_left hp.tl_sub) (by omega_using [hb])
  · have o := c.out
    rw [aT, aL] at o
    rw [Proof.AesXts.Unit.crypt_one_of o,
      hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp), h.mem,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left (sub_trans t_sub s_sub)).sub_right hp.lb_sub) (by decide), htw]
  · rw [call_keeps hp (X := ⟨Da s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_using [])) (by rw [aL]; exact hp.hd_l)
      tS h.inv.esp c (by dsimp only; have := hp.wrapD; omega_using [this]), h.mem]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega_using [this])
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub (by rw [aL]; exact tl_l) tS h.inv.esp c
      (by dsimp only; omega_using [hb]), h.mem]

/-- The postcondition, from the bytes of the data unit. -/
theorem unit_post {enc : Bool} {s' : State}
    (hd : bytesAt s'.mem (Da s₀) (Len s₀) = withOf enc (ciph s₀ enc) (t0 s₀) (bytesAt s₀.mem (Da s₀) (Len s₀))) :
    (unitX86 enc).post s₀ s' := by
  intro key hk
  have hk' := Proof.AesXts.Unit.keys_of (bytesAt s₀.mem ((I s₀).setWidth 64) 16) hk
  have hl : 16 ≤ (bytesAt s₀.mem (Da s₀) (Len s₀)).length := by
    rw [Proof.AesXts.Unit.length_bytesAt]; exact hp.len_lo
  cases enc
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsDecrypt_eq hk' hl, hd]; rfl
  · rw [xtsOf, Proof.AesXts.Unit.aesXtsEncrypt_eq hk' hl, hd]; rfl

/-- The arguments of the call on the whole blocks. -/
theorem ready_wp {s : State} (h : TwPost s₀ s) : WP isa (.block argsAll) s (BlocksReady s₀ (M s₀)) :=
  blk (argsAll_wp (Inv.args hp h.inv) fun s₂ c ax cx dx bx di bp => WP.block_nil (by
    have h₂ := TwPost.keep hp h (c.gpr _ (by decide)) c.mem c.rd c.wr
    exact ⟨h₂, xpre_blocks hp h₂.inv.rd h₂.inv.wr h₂.inv.esp (N := M s₀) (by rw [len_eq s₀]; omega_using []) ax
      (by rw [cx, r_ofNat]) dx bx di bp⟩))

theorem splitAll_wp {enc : Bool} {N : Nat} {s : State} (h : AllPost enc s₀ N s) :
    WP isa (.block split) s (SplitPost enc s₀ N) :=
  blk (split_wp (Inv.args hp h.inv) fun _ c si zf => WP.block_nil
    ⟨AllPost.keep hp h (c.gpr _ (by decide)) c.mem c.rd c.wr, si, zf⟩)

omit hp in
/-- The data unit of whole blocks, after the call on all of them. -/
theorem whole_fin {enc : Bool} {s : State} (h : AllPost enc s₀ (M s₀) s) (hb : B s₀ = 0) : Fin enc s₀ s := by
  refine ⟨h.inv, ?_⟩
  rw [show Len s₀ = 16 * M s₀ by rw [len_eq s₀, hb, Nat.add_zero]]
  cases enc
  · exact Proof.AesXts.Unit.dec_whole h.out
  · exact Proof.AesXts.Unit.enc_whole h.out

omit hp in
theorem eval_b {s : State} (h : s.zf = some (decide (B s₀ = 0))) : isa.eval .e s = some (decide (B s₀ = 0)) := by
  show VG.X86.eval .e s = _; rw [Proof.MdStream.X86.eval_e, h]

theorem encrypt_wp {f : Impl.Aes.X86.Blocks} (hf : XFn true f) :
    WP isa (encrypt f) s₀ fun s' => abiPreserved s₀ s' ∧ (unitX86 true).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp hf) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ready_wp hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (blocks_call hp hf (by rw [len_eq s₀]; omega_using []) h₂.tw h₂.pre) fun s₃ ⟨h₃, _⟩ => ?_)
  refine WP.seq (WP.mono (splitAll_wp hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b h₄.zf)
    (fun hb => WP.block_nil (whole_fin h₄.all (by simpa using hb)))
    (fun hb => steal_wp hp h₄.all.inv h₄.esi (by simpa using hb) fun _ h' =>
      encLastCall_wp hp hf h' h₄.all.mem (by simpa using hb))) fun s₅ h₅ => ?_)
  exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.X86.Unit

end

end


/-!
# XTS-AES of data units on x86: decryption

`decrypt_wp`: the tweak; without a partial block the call on the whole
blocks; with one, the call on the first `M - 1`, the tweak of block `M` at
`zO` and the call on the last whole block from it (`PP`), the swap and the
call on the last whole block from the tweak of block `M - 1`; then the
epilogue. `esi` keeps `B` throughout.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86.Unit

open VG VG.X86 VG.Impl.AesXts.X86Unit
open VG.Proof.AesXts.Unit (swapMem encWith decWith)
open VG.Spec.Aes (bytesAt)

/-- Before the call on the last whole block from the tweak of block `M`,
which is at `zO`. -/
structure DecL1 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  pre : XPre s (W s₀) (Zv s₀) (Lv s₀) (S s₀) 1 (R s₀)
  mem : ∃ m, AllMem false s₀ (M s₀ - 1) m ∧ Frame [⟨Zp s₀, 16⟩] m s.mem ∧
    bytesAt s.mem (Zp s₀) 16 = Spec.Xts.mulAlpha (bytesAt m (Tp s₀) 16)
  esi : s.gpr .esi = BitVec.ofNat 32 (B s₀)

/-- The memory after the call on the last whole block from the tweak of
block `M`: `PP` there, from the memory `m` after the first `M - 1` blocks. -/
def DecMem (s₀ : State) (m₅ : Mem) : Prop :=
  ∃ m, AllMem false s₀ (M s₀ - 1) m ∧
    bytesAt m₅ (L s₀) 16 = Spec.Xts.block (ciph s₀ false) (Spec.Xts.next (t0 s₀) (M s₀)) (bytesAt m (L s₀) 16) ∧
    bytesAt m₅ (Da s₀) (16 * (M s₀ - 1)) = bytesAt m (Da s₀) (16 * (M s₀ - 1)) ∧
    bytesAt m₅ (L s₀ + 16) (B s₀) = bytesAt m (L s₀ + 16) (B s₀) ∧
    bytesAt m₅ (Tp s₀) 16 = Spec.Xts.next (t0 s₀) (M s₀ - 1)

/-- After the call on the last whole block from the tweak of block `M`. -/
structure DecL2 (s₀ s : State) : Prop where
  inv : Inv s₀ s
  mem : DecMem s₀ s.mem
  esi : s.gpr .esi = BitVec.ofNat 32 (B s₀)

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- The arguments of the call on all but the last whole block. -/
theorem head_wp {s : State} (h : TwPost s₀ s) :
    WP isa (.block argsHead) s fun s' => BlocksReady s₀ (M s₀ - 1) s' ∧ s'.gpr .esi = s.gpr .esi :=
  blk (argsHead_wp (Inv.args hp h.inv) hp.m_pos fun s₂ c ax cx dx bx di bp => WP.block_nil (by
    have h₂ := TwPost.keep hp h (c.gpr _ (by decide)) c.mem c.rd c.wr
    exact ⟨⟨h₂, xpre_blocks hp h₂.inv.rd h₂.inv.wr h₂.inv.esp (N := M s₀ - 1) (by rw [len_eq s₀]; omega_using []) ax
      (by rw [cx, r_ofNat]) dx bx di bp⟩, c.gpr _ (by decide)⟩))

/-- The tweak of block `M`, at `zO`, and the arguments of the call on the
last whole block from it. -/
theorem decL1_wp {s₂ : State} (h₂ : AllPost false s₀ (M s₀ - 1) s₂) (hsi : s₂.gpr .esi = BitVec.ofNat 32 (B s₀)) :
    WP isa (.block (nextT ++ argsL zO)) s₂ (DecL1 s₀) := by
  refine nextT_wp hp (Inv.args hp h₂.inv) h₂.inv.wr fun s₃ c₃ => ?_
  have f₃ : Frame [⟨Zp s₀, 16⟩] s₂.mem s₃.mem := by
    rw [c₃.mem]; exact (copy4_frame _ _ _).trans (Proof.AesXts.X86.alphaMem_frame _ _)
  have inv₃ : Inv s₀ s₃ := Inv.step hp h₂.inv (rs := [⟨Zp s₀, 16⟩]) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact .inr (.inl z_sub)) f₃ (c₃.gpr _ (by decide)) c₃.rd c₃.wr
  have si₃ : s₃.gpr .esi = BitVec.ofNat 32 (B s₀) := by rw [c₃.gpr _ (by decide), hsi]
  refine blk (argsL_wp (o := zO) (Inv.args hp inv₃) hp si₃ fun s₆ c₆ ax cx dx bx di bp => WP.block_nil ?_)
  have inv₆ : Inv s₀ s₆ := Inv.step hp inv₃ (rs := []) (fun _ h => by simp at h)
    (by rw [c₆.mem]; exact Frame.refl _ _) (c₆.gpr _ (by decide)) c₆.rd c₆.wr
  refine ⟨inv₆, xpre_last hp inv₆.rd inv₆.wr inv₆.esp (.inr rfl) ax (by rw [cx, r_ofNat]) dx bx di bp,
    ⟨s₂.mem, h₂.mem, by rw [c₆.mem]; exact f₃, ?_⟩, by rw [c₆.gpr _ (by decide), si₃]⟩
  rw [c₆.mem, c₃.mem, Proof.AesXts.X86.alphaMem_bytes, copy4_bytes]

/-- The call on the last whole block from the tweak of block `M`. -/
theorem decL2_wp {d : Impl.Aes.X86.Blocks} (hf : XFn false d) {s : State} (h : DecL1 s₀ s) :
    WP isa (xcall d) s (DecL2 s₀) := by
  have hm := hp.m_pos
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  obtain ⟨m, ⟨hout, htw, hfr⟩, f₃, z₃⟩ := h.mem
  have aZ := hp.scrW (d := zO) (by decide)
  have aL := hp.lA
  refine WP.mono (xts_call false hf.ok hf.nosp hf.stack h.pre) fun s₇ c₇ => ?_
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub s_sub
  have zL : Region.Sub ⟨Zp s₀, 16⟩ (scrR s₀) := sub_trans z_sub s_sub
  have zL' : Region.Sub ⟨(Zv s₀).setWidth 64, 16⟩ (scrR s₀) := by rw [aZ]; exact zL
  have eW := hp.sched_frame h.inv.frame (fun r hr => by simp at hr; rcases hr with rfl | rfl | rfl <;> simp)
  refine ⟨Inv.call hp h.inv (by rw [aZ]; exact z_sub) (.inl (by rw [aL]; exact hp.l_sub)) c₇,
    ⟨m, ⟨hout, htw, hfr⟩, ?_, ?_, ?_, ?_⟩, by rw [c₇.saved .esi (by simp [calleeSaved]), h.esi]⟩
  · have o := c₇.out
    rw [aZ, aL] at o
    rw [Proof.AesXts.Unit.crypt_one_of o, eW, z₃, htw, ← Proof.AesXts.next_succ,
      Nat.sub_add_cancel hm,
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.sub_left hp.l_sub).sub_right zL) (by decide)]
  · rw [call_keeps hp (X := ⟨Da s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_using [])) (by rw [aL]; exact hp.hd_l) zL'
      h.inv.esp c₇ (by dsimp only; have := hp.wrapD; omega_using [this])]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left (blocks_sub (by omega_using []))).sub_right zL) (by dsimp only; have := hp.wrapD; omega_using [this])
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub (by rw [aL]; exact tl_l) zL' h.inv.esp c₇
      (by dsimp only; omega_using [hb])]
    exact Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left hp.tl_sub).sub_right zL) (by dsimp only; omega_using [hb])
  · rw [Proof.Cmac.bytesAt_frame c₇.frame (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [aZ]; exact hp.t_z
        · rw [aL]; exact (hp.data_scr.symm.sub_left tL).sub_right hp.l_sub
        · exact hp.t_wk
        · rw [hp.stk_eq h.inv.esp]; exact (hp.stk_scr.sub_right tL).symm) (by decide),
      Proof.Cmac.bytesAt_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.t_z) (by decide), htw]

/-- The call on the last whole block from the tweak of block `M - 1`, and
the data unit's plaintext. -/
theorem decLast_wp {d : Impl.Aes.X86.Blocks} (hf : XFn false d) {s : State} {m₅ : Mem}
    (h : LastReady tO s₀ s m₅) (hm₅ : DecMem s₀ m₅) (hB : B s₀ ≠ 0) :
    WP isa (xcall d) s (Fin false s₀) := by
  have hb : B s₀ < 16 := Nat.mod_lt _ (by decide)
  have hm := hp.m_pos
  obtain ⟨m, ⟨hout, htw, hfr⟩, h5L, h5H, h5T, tw₅⟩ := hm₅
  have aT := hp.scrW (d := tO) (by decide)
  have aL := hp.lA
  refine WP.mono (xts_call false hf.ok hf.nosp hf.stack h.pre) fun s₁₂ c₁₂ => ?_
  refine ⟨Inv.call hp h.inv (by rw [aT]; exact t_sub) (.inl (by rw [aL]; exact hp.l_sub)) c₁₂, ?_⟩
  have sw := Proof.AesXts.Unit.swapMem_frame m₅ (L s₀) (B s₀)
  have tL : Region.Sub ⟨Tp s₀, 16⟩ (scrR s₀) := sub_trans t_sub s_sub
  have tL' : Region.Sub ⟨(S s₀ + BitVec.ofNat 32 tO).setWidth 64, 16⟩ (scrR s₀) := by rw [aT]; exact tL
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
      · exact hp.stk_data.symm.sub_left hp.tl_sub) (by omega_using [hb])
  · have o := c₁₂.out
    rw [aT, aL] at o
    rw [Proof.AesXts.Unit.crypt_one_of o, eW', h.mem,
      Proof.Cmac.bytesAt_frame sw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.data_scr.symm.sub_left tL).sub_right hp.lb_sub) (by decide), tw₅]
  · rw [call_keeps hp (X := ⟨Da s₀, 16 * (M s₀ - 1)⟩) (blocks_sub (by omega_using [])) (by rw [aL]; exact hp.hd_l) tL'
      h.inv.esp c₁₂ (by dsimp only; have := hp.wrapD; omega_using [this]), h.mem]
    exact Proof.Cmac.bytesAt_frame sw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.hd_lb) (by dsimp only; have := hp.wrapD; omega_using [this])
  · rw [call_keeps hp (X := ⟨L s₀ + 16, B s₀⟩) hp.tl_sub (by rw [aL]; exact tl_l) tL' h.inv.esp c₁₂
      (by dsimp only; omega_using [hb]), h.mem]

/-- The steal of decryption, after the tweak. -/
theorem decSteal_wp {d : Impl.Aes.X86.Blocks} (hf : XFn false d) {s : State} (h : TwPost s₀ s)
    (hsi : s.gpr .esi = BitVec.ofNat 32 (B s₀)) (hB : B s₀ ≠ 0) : WP isa (decSteal d) s (Fin false s₀) := by
  refine WP.seq (WP.mono (head_wp hp h) fun s₁ ⟨h₁, e₁⟩ => ?_)
  refine WP.seq (WP.mono (blocks_call hp hf (by rw [len_eq s₀]; omega_using []) h₁.tw h₁.pre) fun s₂ ⟨h₂, e₂⟩ => ?_)
  refine WP.seq (WP.mono (decL1_wp hp h₂ (by rw [e₂, e₁, hsi])) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (decL2_wp hp hf h₃) fun s₄ h₄ => ?_)
  exact steal_wp hp h₄.inv h₄.esi hB fun _ h' => decLast_wp hp hf h' h₄.mem hB

theorem split_tw_wp {s : State} (h : TwPost s₀ s) :
    WP isa (.block split) s fun s' =>
      TwPost s₀ s' ∧ s'.gpr .esi = BitVec.ofNat 32 (B s₀) ∧ s'.zf = some (decide (B s₀ = 0)) :=
  blk (split_wp (Inv.args hp h.inv) fun _ c si zf => WP.block_nil
    ⟨TwPost.keep hp h (c.gpr _ (by decide)) c.mem c.rd c.wr, si, zf⟩)

theorem decrypt_wp {e d : Impl.Aes.X86.Blocks} (he : XFn true e) (hd : XFn false d) :
    WP isa (decrypt e d) s₀ fun s' => abiPreserved s₀ s' ∧ (unitX86 false).post s₀ s' := by
  refine WP.seq (WP.mono (tweak_wp hp he) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (split_tw_wp hp h₁) fun s₂ ⟨h₂, si₂, z₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.ite (decide (B s₀ = 0)) (eval_b z₂) (fun hb => ?_)
    (fun hb => decSteal_wp hp hd h₂ si₂ (by simpa using hb))) fun s₅ h₅ => ?_)
  · refine WP.seq (WP.mono (ready_wp hp h₂) fun s₃ h₃ => ?_)
    exact WP.mono (blocks_call hp hd (by rw [len_eq s₀]; omega_using []) h₃.tw h₃.pre)
      fun s₄ h₄ => whole_fin h₄.1 (by simpa using hb)
  · exact WP.mono (fin_wp hp h₅.inv) fun s' ⟨g, m⟩ => ⟨g, unit_post hp (by rw [m]; exact h₅.data)⟩

end

end VG.Proof.AesXts.X86.Unit
