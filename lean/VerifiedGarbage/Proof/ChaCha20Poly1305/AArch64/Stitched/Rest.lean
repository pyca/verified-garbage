import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stages
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Bulk
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Blocks
import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitch.Lit
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Xor

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Parts`. -/
section

/-!
# ChaCha20-Poly1305 on AArch64, stitched: the parts around the chunks

`polyIn` and `polyOut` (`Impl/ChaCha20Poly1305/AArch64/Stitched.lean`), and
`Inv0`: the invariant `Inv` without the registers `x22`–`x25`, which the
stitched code reuses.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (Upd Mupd wp_addImm wp_subImm wp_mov wp_movz wp_str wp_ldr)
open VG.Spec.Poly1305 (Repr bytesAt)

variable {e : Bool}

theorem write_write_x (s : State) (d : Reg) (a b : BitVec 64) :
    (s.write .x d a).write .x d b = s.write .x d b := by
  simp only [State.write]; congr 1; funext r; split <;> rfl

set_option simprocs false in
theorem const64_run (d : Reg) (c : BitVec 64) (s : State) :
    WP isa (.block (VG.Impl.Poly1305.AArch64.const64 d c)) s fun u => u = s.write .x d c := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [VG.Impl.Poly1305.AArch64.const64, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.read, Size.bits, BitVec.setWidth_eq, ite_true, Option.some.injEq,
    exists_eq_left', RegUpd.gpr_write_self, VG.Proof.ChaCha20Poly1305.AArch64.write_write_x, movz_movk64']

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_and {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and .x d n m :: is)) s Q :=
  VG.Proof.ChaCha20.AArch64.Xor.WP.cons (s' := s.write .x d (s.gpr n &&& s.gpr m))
    (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_const64 {d : Reg} {c : BitVec 64}
    (k : ∀ s', Upd s s' d c → WP isa (.block is) s' Q) :
    WP isa (.block (VG.Impl.Poly1305.AArch64.const64 d c ++ is)) s Q :=
  WP.block_append ((VG.Proof.ChaCha20Poly1305.AArch64.const64_run d c s).mono fun u hu => by subst hu; exact k _ (Upd.write64 _ _ _))

end

/-- `Inv` without `x22`–`x25`. -/
structure Inv0 (s₀ : State) (s : State) : Prop where
  x21 : s.gpr .x21 = cx s₀
  un : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved s₀ s.mem
  frame : Frame [workR s₀, dR s₀] s₀.mem s.mem

theorem Inv.inv0 {s₀ s : State} (h : Inv s₀ s) : VG.Proof.ChaCha20Poly1305.AArch64.Inv0 s₀ s :=
  ⟨h.x21, h.un, h.sp, h.rd, h.wr, h.saved, h.frame⟩

theorem Inv0.step {s₀ s s' : State} {rs : List Region} (h : VG.Proof.ChaCha20Poly1305.AArch64.Inv0 s₀ s) (hk : Kept rs s s')
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [workR s₀, dR s₀], Region.Sub r r')
    (hsv : ∀ r ∈ rs, (sub s₀ 576 56).Disjoint r) : VG.Proof.ChaCha20Poly1305.AArch64.Inv0 s₀ s' where
  x21 := by rw [hk.cs _ (pres .x21) (pres30 .x21), h.x21]
  un r hr := by
    rw [hk.cs _ (untouched_preserved r hr).1 (untouched_preserved r hr).2, h.un r hr]
  sp := by rw [hk.sp, h.sp]
  rd := by rw [hk.rd, h.rd]
  wr := by rw [hk.wr, h.wr]
  saved := h.saved.frame hk.frame hsv
  frame := h.frame.trans (hk.frame.sub hsub)

theorem mac_inv0 {s₀ s s' : State} (h : VG.Proof.ChaCha20Poly1305.AArch64.Inv0 s₀ s) (hk : Kept (macR s₀) s s') : VG.Proof.ChaCha20Poly1305.AArch64.Inv0 s₀ s' :=
  h.step hk (macR_work s₀) (macR_saved s₀)

/-- The lengths block absorbed. -/
theorem absorbLengths_ok0 {s₀ : State} (hp : APre e s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.AArch64.Inv0 s₀ s) :
    WP isa absorbLengths s fun s' => VG.Proof.ChaCha20Poly1305.AArch64.Inv0 s₀ s' ∧ Kept (macR s₀) s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        Repr s'.mem (off (cx s₀) 448) key (msg ++ bytesAt s.mem (off (cx s₀) 0) 16) := by
  unfold absorbLengths
  refine WP.seq (WP.mono (ptrs3_ok (a := 448) (b := 0) (by lit_omega) (by lit_omega) 1 s)
    fun s₁ ⟨h0, h1, h2, k₁⟩ => ?_)
  rw [h.x21] at h0 h1
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, h.wr]
  have m₁ := k₁.mem_eq
  refine blocks_call (n := 1) h0 h1 h2 (by lit_omega)
    (sub_disj s₀ (b := 0) (m := 16 * 1) (by lit_omega) (by lit_omega) (by lit_omega))
    (by rw [hp.off_toNat (by lit_omega)]; have := hp.wrap_c; omega)
    (covers2 hp wr₁ (a := 448) (n := 128) (b := 0) (m := 16 * 1) (by lit_omega) (by lit_omega))
    (covers1 hp wr₁ (a := 448) (n := 128) (by lit_omega)) fun s₂ k₂ repr₂ => ?_
  have hk : Kept (macR s₀) s s₂ :=
    (kept_mac0 k₁).trans (kept_mac (k := 448) (n := 128) (by lit_omega) (by lit_omega) k₂)
  exact ⟨VG.Proof.ChaCha20Poly1305.AArch64.mac_inv0 h hk, hk, fun key msg hr => by rw [← m₁]; exact repr₂ key msg (by rw [m₁]; exact hr)⟩

/-- The tag written to `ctx[out, out + 16)`. -/
theorem finalizeTo_ok0 {s₀ : State} (hp : APre e s₀) {s : State} (h : VG.Proof.ChaCha20Poly1305.AArch64.Inv0 s₀ s) {out : Nat}
    (hout : out + 16 ≤ 448) :
    WP isa (finalizeTo out) s fun s' => Kept [sub s₀ 448 128, sub s₀ out 16] s s' ∧
      ∀ key msg, Repr s.mem (off (cx s₀) 448) key msg →
        bytesAt s'.mem (off (cx s₀) out) 16 = Spec.Poly1305.mac key msg := by
  unfold finalizeTo
  refine WP.seq (WP.mono (fptrs_ok (out := out) (by lit_omega) s) fun s₁ ⟨h0, h1, h2, k₁⟩ => ?_)
  rw [h.x21] at h0 h2
  have wr₁ : s₁.wr = s₀.wr := by rw [k₁.wr, h.wr]
  have m₁ := k₁.mem_eq
  have ho : out + 16 ≤ 760 := by omega
  refine finalize_call h0 h1 h2 (sub_disj s₀ (by lit_omega) (by lit_omega) ho)
    (Covers.right (covers_sub hp wr₁ _ (by
      intro r hr; simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨448, rfl, show 448 + 128 ≤ 760 by omega⟩
      · exact ⟨out, rfl, ho⟩)))
    (covers_sub hp wr₁ _ (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨448, rfl, show 448 + 128 ≤ 760 by omega⟩
      · exact ⟨out, rfl, ho⟩))
    fun s₂ k₂ tag₂ => ?_
  exact ⟨(k₁.sub fun _ hr => absurd hr List.not_mem_nil).trans k₂,
    fun key msg hr => tag₂ key msg (by rw [m₁]; exact hr)⟩

/-- The clamping masks. -/
abbrev M0 : BitVec 64 := 0x0ffffffc0fffffff
abbrev M1 : BitVec 64 := 0x0ffffffc0ffffffc

/-- The memory `polyIn` leaves: `x27`, `x28` and the clamped key stored. -/
def memIn (m : Mem) (c : Addr) (a b : BitVec 64) : Mem :=
  (((m.writeW (off c 32) a).writeW (off c 40) b).writeW (off c 288)
    (m.readW (off c 472) 64 &&& VG.Proof.ChaCha20Poly1305.AArch64.M0)).writeW (off c 296) (m.readW (off c 480) 64 &&& VG.Proof.ChaCha20Poly1305.AArch64.M1)

theorem polyIn_core {s₀ : State} (hp : APre e s₀) {s : State} (hx21 : s.gpr .x21 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block polyIn) s fun u =>
      u.gpr .x21 = s.mem.readW (off (cx s₀) 448) 64 ∧ u.gpr .x22 = s.mem.readW (off (cx s₀) 456) 64 ∧
      u.gpr .x23 = s.mem.readW (off (cx s₀) 464) 64 ∧
      u.mem = VG.Proof.ChaCha20Poly1305.AArch64.memIn s.mem (cx s₀) (s.gpr .x27) (s.gpr .x28) ∧
      (∀ r, r ∉ [Reg.x21, .x22, .x23, .x24, .x25] → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr := by
  have o (d : Nat) (hd : d + 8 ≤ 760) : InRegions s.wr (off (cx s₀) d) 8 := by
    rw [hwr]; exact hp.in_ctx hd
  have i (d : Nat) (hd : d + 8 ≤ 760) : InRegions (s.rd ++ s.wr) (off (cx s₀) d) 8 := by
    rw [hrd, hwr]; exact hp.in_ctx' hd
  unfold polyIn
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_str (a := off (cx s₀) 32) (by decide) (by rw [hx21]) (o 32 (by lit_omega)) fun s₁ g₁ => ?_
  refine wp_str (a := off (cx s₀) 40) (by decide) (by rw [g₁.gpr, hx21])
    (by rw [g₁.wr]; exact o 40 (by lit_omega)) fun s₂ g₂ => ?_
  refine VG.Proof.ChaCha20Poly1305.AArch64.wp_const64 fun s₃ u₃ => ?_
  have x21₃ : s₃.gpr .x21 = cx s₀ := by rw [u₃.other _ (by decide), g₂.gpr, g₁.gpr, hx21]
  have rw₃ : s₃.rd ++ s₃.wr = s.rd ++ s.wr := by rw [u₃.rd, u₃.wr, g₂.rd, g₂.wr, g₁.rd, g₁.wr]
  refine wp_ldr (a := off (cx s₀) 472) (by decide) (by rw [x21₃]) (by rw [rw₃]; exact i 472 (by lit_omega))
    fun s₄ u₄ => ?_
  refine VG.Proof.ChaCha20Poly1305.AArch64.wp_and fun s₅ u₅ => ?_
  refine wp_str (a := off (cx s₀) 288) (by decide) (by rw [u₅.other _ (by decide), u₄.other _ (by decide), x21₃])
    (by rw [u₅.wr, u₄.wr, u₃.wr, g₂.wr, g₁.wr]; exact o 288 (by lit_omega)) fun s₆ g₆ => ?_
  refine VG.Proof.ChaCha20Poly1305.AArch64.wp_const64 fun s₇ u₇ => ?_
  have x21₇ : s₇.gpr .x21 = cx s₀ := by
    rw [u₇.other _ (by decide), g₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), x21₃]
  have rw₇ : s₇.rd ++ s₇.wr = s.rd ++ s.wr := by rw [u₇.rd, u₇.wr, g₆.rd, g₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, rw₃]
  refine wp_ldr (a := off (cx s₀) 480) (by decide) (by rw [x21₇]) (by rw [rw₇]; exact i 480 (by lit_omega))
    fun s₈ u₈ => ?_
  refine VG.Proof.ChaCha20Poly1305.AArch64.wp_and fun s₉ u₉ => ?_
  refine wp_str (a := off (cx s₀) 296) (by decide) (by rw [u₉.other _ (by decide), u₈.other _ (by decide), x21₇])
    (by rw [u₉.wr, u₈.wr, u₇.wr, g₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, g₁.wr]; exact o 296 (by lit_omega))
    fun s₁₀ g₁₀ => ?_
  have x21₁₀ : s₁₀.gpr .x21 = cx s₀ := by
    rw [g₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), x21₇]
  have rw₁₀ : s₁₀.rd ++ s₁₀.wr = s.rd ++ s.wr := by rw [g₁₀.rd, g₁₀.wr, u₉.rd, u₉.wr, u₈.rd, u₈.wr, rw₇]
  refine wp_ldr (a := off (cx s₀) 456) (by decide) (by rw [x21₁₀]) (by rw [rw₁₀]; exact i 456 (by lit_omega))
    fun s₁₁ u₁₁ => ?_
  refine wp_ldr (a := off (cx s₀) 464) (by decide) (by rw [u₁₁.other _ (by decide), x21₁₀])
    (by rw [u₁₁.rd, u₁₁.wr, rw₁₀]; exact i 464 (by lit_omega)) fun s₁₂ u₁₂ => ?_
  refine wp_ldr (a := off (cx s₀) 448) (by decide)
    (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), x21₁₀])
    (by rw [u₁₂.rd, u₁₂.wr, u₁₁.rd, u₁₁.wr, rw₁₀]; exact i 448 (by lit_omega)) fun s₁₃ u₁₃ => ?_
  have m₂ : s₂.mem = (s.mem.writeW (off (cx s₀) 32) (s.gpr .x27)).writeW (off (cx s₀) 40) (s.gpr .x28) := by
    rw [g₂.mem, g₁.mem, g₁.gpr]
  have r472 : s₃.mem.readW (off (cx s₀) 472) 64 = s.mem.readW (off (cx s₀) 472) 64 := by
    rw [u₃.mem, m₂, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
      readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega)]
  have m₆ : s₆.mem = s₂.mem.writeW (off (cx s₀) 288) (s.mem.readW (off (cx s₀) 472) 64 &&& VG.Proof.ChaCha20Poly1305.AArch64.M0) := by
    rw [g₆.mem, u₅.mem, u₄.mem, u₃.mem, u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.gpr, ← u₃.mem, r472]
  have r480 : s₇.mem.readW (off (cx s₀) 480) 64 = s.mem.readW (off (cx s₀) 480) 64 := by
    rw [u₇.mem, m₆, m₂, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
      readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
      readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega)]
  have m₁₀ : s₁₀.mem = VG.Proof.ChaCha20Poly1305.AArch64.memIn s.mem (cx s₀) (s.gpr .x27) (s.gpr .x28) := by
    rw [g₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₉.gpr, u₈.gpr, u₈.other _ (by decide), u₇.gpr, ← u₇.mem, r480,
      u₇.mem, m₆, m₂]
    rfl
  have rd (d : Nat) (hd : d = 448 ∨ d = 456 ∨ d = 464) :
      s₁₀.mem.readW (off (cx s₀) d) 64 = s.mem.readW (off (cx s₀) d) 64 := by
    rw [m₁₀, VG.Proof.ChaCha20Poly1305.AArch64.memIn]
    rcases hd with rfl | rfl | rfl <;>
      rw [readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
        readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
        readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
        readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega)]
  refine WP.block_nil ⟨?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [u₁₃.gpr, u₁₂.mem, u₁₁.mem, rd 448 (by decide)]
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, rd 456 (by decide)]
  · rw [u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.mem, rd 464 (by decide)]
  · rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₁₃.other _ hr.1, u₁₂.other _ hr.2.2.1, u₁₁.other _ hr.2.1, g₁₀.gpr, u₉.other _ hr.2.2.2.2,
      u₈.other _ hr.2.2.2.2, u₇.other _ hr.2.2.2.1, g₆.gpr, u₅.other _ hr.2.2.2.2,
      u₄.other _ hr.2.2.2.2, u₃.other _ hr.2.2.2.1, g₂.gpr, g₁.gpr]
  · rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, g₁₀.rd, u₉.rd, u₈.rd, u₇.rd, g₆.rd, u₅.rd, u₄.rd, u₃.rd, g₂.rd, g₁.rd]
  · rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, g₁₀.wr, u₉.wr, u₈.wr, u₇.wr, g₆.wr, u₅.wr, u₄.wr, u₃.wr, g₂.wr, g₁.wr]

theorem polyIn_ok {s₀ : State} (hp : APre e s₀) {s : State} (hx21 : s.gpr .x21 = cx s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block polyIn) s fun u =>
      (u.gpr .x21 = s.mem.readW (off (cx s₀) 448) 64 ∧ u.gpr .x22 = s.mem.readW (off (cx s₀) 456) 64 ∧
      u.gpr .x23 = s.mem.readW (off (cx s₀) 464) 64 ∧
      u.mem = VG.Proof.ChaCha20Poly1305.AArch64.memIn s.mem (cx s₀) (s.gpr .x27) (s.gpr .x28) ∧
      (∀ r, r ∉ [Reg.x21, .x22, .x23, .x24, .x25] → u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr) ∧ u.v = s.v ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr :=
  VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by decide +kernel) (VG.Proof.ChaCha20Poly1305.AArch64.polyIn_core hp hx21 hrd hwr)

/-- The accumulator's value in `x21`–`x23`. -/
abbrev hacc (s : State) : Nat :=
  (s.gpr .x21).toNat + 2 ^ 64 * (s.gpr .x22).toNat + 2 ^ 128 * (s.gpr .x23).toNat

/-- The data not yet absorbed, after the chunks. -/
def restP (enc : Bool) (x1 x2 : BitVec 64) : BitVec 64 × BitVec 64 :=
  if enc then (x1 - 512#64, x2 + 512#64) else (x1, x2)

theorem polyOut_core {s₀ : State} (hp : APre e s₀) (enc : Bool) {s : State}
    (hx0 : s.gpr .x0 = off (cx s₀) 64) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block (polyOut enc)) s fun u =>
      ((s.gpr .x23).toNat ≤ 4 →
        Poly1305.AArch64.Radix64.hval u = VG.Proof.ChaCha20Poly1305.AArch64.hacc s % Spec.Poly1305.P) ∧
      u.mem = Poly1305.AArch64.storeHm s.mem (off (cx s₀) 448) (u.gpr .x4) (u.gpr .x5) (u.gpr .x6) ∧
      u.gpr .x21 = cx s₀ ∧ u.gpr .x27 = s.mem.readW (off (cx s₀) 32) 64 ∧
      u.gpr .x28 = s.mem.readW (off (cx s₀) 40) 64 ∧
      u.gpr .x22 = (VG.Proof.ChaCha20Poly1305.AArch64.restP enc (s.gpr .x1) (s.gpr .x2)).1 ∧
      u.gpr .x23 = (VG.Proof.ChaCha20Poly1305.AArch64.restP enc (s.gpr .x1) (s.gpr .x2)).2 ∧
      (∀ r, r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23, .x27, .x28] →
        u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr := by
  have o (d : Nat) (hd : d + 8 ≤ 760) : InRegions s₀.wr (off (cx s₀) d) 8 := hp.in_ctx hd
  have i (d : Nat) (hd : d + 8 ≤ 760) : InRegions (s₀.rd ++ s₀.wr) (off (cx s₀) d) 8 := hp.in_ctx' hd
  have hc : off (cx s₀) 64 - BitVec.ofNat 64 64 = cx s₀ := BitVec.add_sub_cancel _ _
  unfold polyOut
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => ?_
  refine WP.block_append (WP.mono (Poly1305.AArch64.Radix64.reduce_ok s₃) fun s₄ ⟨e₄, k₄⟩ => ?_)
  have g₃ (r : Reg) (h4 : r ≠ .x4) (h5 : r ≠ .x5) (h6 : r ≠ .x6) : s₃.gpr r = s.gpr r := by
    rw [u₃.other _ h6, u₂.other _ h5, u₁.other _ h4]
  have m₄ : s₄.mem = s.mem := by rw [k₄.2.1, u₃.mem, u₂.mem, u₁.mem]
  have rw₄ : s₄.rd = s.rd ∧ s₄.wr = s.wr := ⟨by rw [k₄.2.2.1, u₃.rd, u₂.rd, u₁.rd],
    by rw [k₄.2.2.2, u₃.wr, u₂.wr, u₁.wr]⟩
  refine wp_subImm (by decide) fun s₅ u₅ => ?_
  have x21₅ : s₅.gpr .x21 = cx s₀ := by
    rw [u₅.gpr, k₄.gpr' (r := .x0), g₃ _ (by decide) (by decide) (by decide), hx0, hc]
  refine wp_str (a := off (cx s₀) 448) (by decide) (by rw [x21₅])
    (by rw [u₅.wr, rw₄.2, hwr]; exact o 448 (by lit_omega)) fun s₆ g₆ => ?_
  refine wp_str (a := off (cx s₀) 456) (by decide) (by rw [g₆.gpr, x21₅])
    (by rw [g₆.wr, u₅.wr, rw₄.2, hwr]; exact o 456 (by lit_omega)) fun s₇ g₇ => ?_
  refine wp_str (a := off (cx s₀) 464) (by decide) (by rw [g₇.gpr, g₆.gpr, x21₅])
    (by rw [g₇.wr, g₆.wr, u₅.wr, rw₄.2, hwr]; exact o 464 (by lit_omega)) fun s₈ g₈ => ?_
  have x21₈ : s₈.gpr .x21 = cx s₀ := by rw [g₈.gpr, g₇.gpr, g₆.gpr, x21₅]
  have rw₈ : s₈.rd ++ s₈.wr = s₀.rd ++ s₀.wr := by
    rw [g₈.rd, g₈.wr, g₇.rd, g₇.wr, g₆.rd, g₆.wr, u₅.rd, u₅.wr, rw₄.1, rw₄.2, hrd, hwr]
  have m₈ : s₈.mem = Poly1305.AArch64.storeHm s.mem (off (cx s₀) 448) (s₄.gpr .x4) (s₄.gpr .x5)
      (s₄.gpr .x6) := by
    rw [g₈.mem, g₇.mem, g₆.mem, u₅.mem, m₄, g₇.gpr, g₆.gpr, u₅.other _ (by decide),
      u₅.other _ (by decide), u₅.other _ (by decide)]
    simp only [Poly1305.AArch64.storeHm, Poly1305.AArch64.off, off, BitVec.add_assoc, ← BitVec.ofNat_add]
  have r8 (d : Nat) (hd : d = 32 ∨ d = 40) :
      s₈.mem.readW (off (cx s₀) d) 64 = s.mem.readW (off (cx s₀) d) 64 := by
    rw [m₈]
    simp only [Poly1305.AArch64.storeHm, Poly1305.AArch64.off, off, BitVec.add_assoc, ← BitVec.ofNat_add]
    rcases hd with rfl | rfl <;>
      rw [readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
        readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
        readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega)]
  refine wp_ldr (a := off (cx s₀) 32) (by decide) (by rw [x21₈]) (by rw [rw₈]; exact i 32 (by lit_omega))
    fun s₉ u₉ => ?_
  refine wp_ldr (a := off (cx s₀) 40) (by decide) (by rw [u₉.other _ (by decide), x21₈])
    (by rw [u₉.rd, u₉.wr, rw₈]; exact i 40 (by lit_omega)) fun s₁₀ u₁₀ => ?_
  have g₁₀ (r : Reg) (h27 : r ≠ .x27) (h28 : r ≠ .x28) : s₁₀.gpr r = s₈.gpr r := by
    rw [u₁₀.other _ h28, u₉.other _ h27]
  have x12 : s₁₀.gpr .x1 = s.gpr .x1 ∧ s₁₀.gpr .x2 = s.gpr .x2 := by
    refine ⟨?_, ?_⟩ <;> rw [g₁₀ _ (by decide) (by decide), g₈.gpr, g₇.gpr, g₆.gpr,
      u₅.other _ (by decide), k₄.gpr', g₃ _ (by decide) (by decide) (by decide)]
  have common : ∀ u : State, (∀ r, r ≠ .x22 → r ≠ .x23 → u.gpr r = s₁₀.gpr r) → u.mem = s₁₀.mem →
      u.rd = s₁₀.rd → u.wr = s₁₀.wr →
      ((s.gpr .x23).toNat ≤ 4 → Poly1305.AArch64.Radix64.hval u = VG.Proof.ChaCha20Poly1305.AArch64.hacc s % Spec.Poly1305.P) ∧
      u.mem = Poly1305.AArch64.storeHm s.mem (off (cx s₀) 448) (u.gpr .x4) (u.gpr .x5) (u.gpr .x6) ∧
      u.gpr .x21 = cx s₀ ∧ u.gpr .x27 = s.mem.readW (off (cx s₀) 32) 64 ∧
      u.gpr .x28 = s.mem.readW (off (cx s₀) 40) 64 ∧
      (∀ r, r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23, .x27, .x28] →
        u.gpr r = s.gpr r) ∧ u.rd = s.rd ∧ u.wr = s.wr := by
    intro u hu hm hr hw
    have h456 (r : Reg) (h : r = .x4 ∨ r = .x5 ∨ r = .x6) : u.gpr r = s₄.gpr r := by
      rcases h with rfl | rfl | rfl <;>
        rw [hu _ (by decide) (by decide), g₁₀ _ (by decide) (by decide), g₈.gpr, g₇.gpr, g₆.gpr,
          u₅.other _ (by decide)]
    refine ⟨fun h23 => ?_, ?_, ?_, ?_, ?_, fun r hr' => ?_, ?_, ?_⟩
    · have a4 : s₃.gpr .x4 = s.gpr .x21 := by
        rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      have a5 : s₃.gpr .x5 = s.gpr .x22 := by
        rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
      have a6 : s₃.gpr .x6 = s.gpr .x23 := by
        rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)]
      have e := e₄ (by rw [a6]; exact h23)
      simp only [Poly1305.AArch64.Radix64.hval, h456 .x4 (by decide), h456 .x5 (by decide),
        h456 .x6 (by decide), a4, a5, a6] at e ⊢
      exact e
    · rw [hm, u₁₀.mem, u₉.mem, m₈, h456 .x4 (by decide), h456 .x5 (by decide), h456 .x6 (by decide)]
    · rw [hu _ (by decide) (by decide), g₁₀ _ (by decide) (by decide), x21₈]
    · rw [hu _ (by decide) (by decide), u₁₀.other _ (by decide), u₉.gpr, r8 32 (by decide)]
    · rw [hu _ (by decide) (by decide), u₁₀.gpr, u₉.mem, r8 40 (by decide)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨h4, h5, h6, h9, h10, h11, h12, h13, h14, h21, h22, h23, h27, h28⟩ := hr'
      have hk : r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨h4, h5, h6, h9, h10, h11, h12, h13, h14⟩
      rw [hu _ h22 h23, g₁₀ _ h27 h28, g₈.gpr, g₇.gpr, g₆.gpr, u₅.other _ h21, k₄.1 r hk, g₃ _ h4 h5 h6]
    · rw [hr, u₁₀.rd, u₉.rd, g₈.rd, g₇.rd, g₆.rd, u₅.rd, rw₄.1]
    · rw [hw, u₁₀.wr, u₉.wr, g₈.wr, g₇.wr, g₆.wr, u₅.wr, rw₄.2]
  cases enc
  · simp only [Bool.false_eq_true, ite_false, VG.Proof.ChaCha20Poly1305.AArch64.restP]
    refine wp_mov fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ => WP.block_nil ?_
    obtain ⟨a, b, c, d, e, f, g, h⟩ := common s₁₂ (fun r h22 h23 => by
      rw [u₁₂.other _ h23, u₁₁.other _ h22]) (by rw [u₁₂.mem, u₁₁.mem]) (by rw [u₁₂.rd, u₁₁.rd])
      (by rw [u₁₂.wr, u₁₁.wr])
    exact ⟨a, b, c, d, e, by rw [u₁₂.other _ (by decide), u₁₁.gpr, x12.1],
      by rw [u₁₂.gpr, u₁₁.other _ (by decide), x12.2], f, g, h⟩
  · simp only [ite_true, VG.Proof.ChaCha20Poly1305.AArch64.restP]
    refine wp_subImm (by decide) fun s₁₁ u₁₁ => wp_addImm (by decide) fun s₁₂ u₁₂ => WP.block_nil ?_
    obtain ⟨a, b, c, d, e, f, g, h⟩ := common s₁₂ (fun r h22 h23 => by
      rw [u₁₂.other _ h23, u₁₁.other _ h22]) (by rw [u₁₂.mem, u₁₁.mem]) (by rw [u₁₂.rd, u₁₁.rd])
      (by rw [u₁₂.wr, u₁₁.wr])
    exact ⟨a, b, c, d, e, by rw [u₁₂.other _ (by decide), u₁₁.gpr, x12.1],
      by rw [u₁₂.gpr, u₁₁.other _ (by decide), x12.2], f, g, h⟩

theorem polyOut_ok {s₀ : State} (hp : APre e s₀) (enc : Bool) {s : State}
    (hx0 : s.gpr .x0 = off (cx s₀) 64) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block (polyOut enc)) s fun u =>
      (((s.gpr .x23).toNat ≤ 4 →
        Poly1305.AArch64.Radix64.hval u = VG.Proof.ChaCha20Poly1305.AArch64.hacc s % Spec.Poly1305.P) ∧
      u.mem = Poly1305.AArch64.storeHm s.mem (off (cx s₀) 448) (u.gpr .x4) (u.gpr .x5) (u.gpr .x6) ∧
      u.gpr .x21 = cx s₀ ∧ u.gpr .x27 = s.mem.readW (off (cx s₀) 32) 64 ∧
      u.gpr .x28 = s.mem.readW (off (cx s₀) 40) 64 ∧
      u.gpr .x22 = (VG.Proof.ChaCha20Poly1305.AArch64.restP enc (s.gpr .x1) (s.gpr .x2)).1 ∧
      u.gpr .x23 = (VG.Proof.ChaCha20Poly1305.AArch64.restP enc (s.gpr .x1) (s.gpr .x2)).2 ∧
      (∀ r, r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23, .x27, .x28] →
        u.gpr r = s.gpr r) ∧
      u.rd = s.rd ∧ u.wr = s.wr) ∧ u.v = s.v ∧ u.sp = s.sp ∧ u.rd = s.rd ∧ u.wr = s.wr :=
  VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by cases enc <;> decide +kernel)
    (VG.Proof.ChaCha20Poly1305.AArch64.polyOut_core hp enc hx0 hrd hwr)

end VG.Proof.ChaCha20Poly1305.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypt`. -/
section

/-!
# ChaCha20-Poly1305 on AArch64, stitched: the chunks in the context

`Stitch.bulk` runs on the regions of the stream (the ChaCha20 state, the data
and the working space, as `vg_chacha20_xor`'s contract gives them), which the
context and the data contain (`WP.narrow`).
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Bulked BPre Acc bulk_ok)
open VG.Spec.Poly1305 (Repr bytesAt)

variable {e : Bool}

variable {sve : Bool}

@[simp] theorem withRegions_v (s : State) (rd wr : List Region) : (s.withRegions rd wr).v = s.v := rfl

/-- The stream's regions in the context. -/
abbrev streamR (s₀ : State) : List Region := [sub s₀ 64 64, dR s₀, sub s₀ 128 320]

theorem bulk_bpre {s₀ : State} (hp : APre e s₀) {s : State} (hx0 : s.gpr .x0 = off (cx s₀) 64)
    (hx1 : s.gpr .x1 = dp s₀) (hx2 : s.gpr .x2 = s₀.gpr .x5) (hx3 : s.gpr .x3 = off (cx s₀) 128) :
    BPre (s.withRegions [] (VG.Proof.ChaCha20Poly1305.AArch64.streamR s₀)) := by
  have hst : (sub s₀ 64 64).Disjoint (dR s₀) := hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
  have hsb : (sub s₀ 64 64).Disjoint (sub s₀ 128 320) :=
    sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
  have hdb : (dR s₀).Disjoint (sub s₀ 128 320) := hp.c_d.symm.sub_right (sub_ctx s₀ (by lit_omega))
  refine ⟨⟨rfl, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [VG.Proof.ChaCha20.AArch64.Xor.stR, VG.Proof.ChaCha20.AArch64.Xor.dR,
      VG.Proof.ChaCha20.AArch64.Xor.bR, VG.Proof.ChaCha20.AArch64.Xor.st,
      VG.Proof.ChaCha20.AArch64.Xor.dp, VG.Proof.ChaCha20.AArch64.Xor.L,
      VG.Proof.ChaCha20.AArch64.Xor.bp, State.withRegions_gpr, State.withRegions_wr, hx0, hx1, hx2,
      hx3] <;>
    first | rfl | exact hst | exact hsb | exact hdb | exact hp.wrap_d |
      simp only [off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The chunks, on the context's regions. -/
theorem bulkA_ok (enc : Bool) {s₀ : State} (hp : APre e s₀) {s : State}
    (hx0 : s.gpr .x0 = off (cx s₀) 64) (hx1 : s.gpr .x1 = dp s₀) (hx2 : s.gpr .x2 = s₀.gpr .x5)
    (hx3 : s.gpr .x3 = off (cx s₀) 128) (hL : 512 ≤ L s₀) (hwr : s.wr = s₀.wr)
    {R a : Nat} (ha : Acc R a s) :
    WP isa (Stitch.bulk sve enc) s fun u => (∃ T, Bulked enc R a (s.withRegions [] (VG.Proof.ChaCha20Poly1305.AArch64.streamR s₀)) T
      (u.withRegions [] (VG.Proof.ChaCha20Poly1305.AArch64.streamR s₀))) ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
      Frame (VG.Proof.ChaCha20Poly1305.AArch64.streamR s₀) s.mem u.mem := by
  have hb := VG.Proof.ChaCha20Poly1305.AArch64.bulk_bpre hp hx0 hx1 hx2 hx3
  have hL' : 512 ≤ VG.Proof.ChaCha20.AArch64.Xor.L (s.withRegions [] (VG.Proof.ChaCha20Poly1305.AArch64.streamR s₀)) := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.L, State.withRegions_gpr, hx2]; exact hL
  have ha' : Acc R a (s.withRegions [] (VG.Proof.ChaCha20Poly1305.AArch64.streamR s₀)) := ⟨ha.h, ha.h2, ha.key, ha.k0, ha.k1⟩
  have hw : Covers (VG.Proof.ChaCha20Poly1305.AArch64.streamR s₀) s.wr := by
    rw [hwr]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, hp.ctx_wr, 64, rfl, by show 64 + 64 ≤ 760; omega⟩
    · exact ⟨dR s₀, hp.d_wr, 0, by simp, by simp⟩
    · exact ⟨ctxR s₀, hp.ctx_wr, 128, rfl, by show 128 + 320 ≤ 760; omega⟩
  refine WP.narrow (bulk_ok enc hb hL' ha') (Covers.right hw) hw ?_ (by cases sve <;> cases enc <;> decide +kernel)
  intro u hrd' hwr' hsp hf hu
  exact ⟨hu, hrd', hwr', hsp, hf⟩

end VG.Proof.ChaCha20Poly1305.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Crypted`. -/
section

/-!
# ChaCha20-Poly1305 on AArch64, stitched: `cryptStitched`

From the state after the lengths, with the ChaCha20 state for counter 0 and
the Poly1305 state for the additional data: after `T` chunks (none for fewer
than 512 bytes), the data's first `512 T` bytes encrypted from counter 1, the
counter advanced past them, the stream's arguments set to the rest, and the
bytes absorbed (`pre`) and the rest's pointer and length in `x22`, `x23`.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20Poly1305.AArch64.Stitch (Bulked Acc rebase rebase_of)
open VG.Proof.ChaCha20 (ctr)
open VG.Proof.Poly1305 (absorbAll)
open VG.Spec.Poly1305 (Repr bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream)

variable {e : Bool}

variable {sve : Bool}

/-- The bytes the chunks absorbed: all of them when decrypting, all but the
last chunk when encrypting. -/
def pre (enc : Bool) (T : Nat) : Nat := if enc then 512 * (T - 1) else 512 * T

theorem pre_le (enc : Bool) (T : Nat) : VG.Proof.ChaCha20Poly1305.AArch64.pre enc T ≤ 512 * T := by
  cases enc <;> simp only [VG.Proof.ChaCha20Poly1305.AArch64.pre, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem pre_zero (enc : Bool) : VG.Proof.ChaCha20Poly1305.AArch64.pre enc 0 = 0 := by cases enc <;> rfl

theorem pre_mod (enc : Bool) (T : Nat) : VG.Proof.ChaCha20Poly1305.AArch64.pre enc T % 16 = 0 := by
  cases enc <;> simp only [VG.Proof.ChaCha20Poly1305.AArch64.pre, Bool.false_eq_true, ite_false, ite_true] <;> omega

/-- The keystream from counter 1. -/
abbrev KS1 (s₀ : State) : List Byte :=
  keystream (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (L s₀)

/-- What `cryptStitched` leaves, after `T` chunks, from `s`. -/
structure Crypted (enc : Bool) (s₀ s : State) (key msg : List Byte) (T : Nat) (u : State) : Prop where
  inv : VG.Proof.ChaCha20Poly1305.AArch64.Inv0 s₀ u
  le : 512 * T ≤ L s₀
  x0 : u.gpr .x0 = off (cx s₀) 64
  x1 : u.gpr .x1 = dp s₀ + BitVec.ofNat 64 (512 * T)
  x2 : u.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * T)
  x3 : u.gpr .x3 = off (cx s₀) 128
  x22 : u.gpr .x22 = dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20Poly1305.AArch64.pre enc T)
  x23 : u.gpr .x23 = BitVec.ofNat 64 (L s₀ - VG.Proof.ChaCha20Poly1305.AArch64.pre enc T)
  cnt : stateAt u.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (8 * T)
  data : ∀ k < L s₀, u.mem (dp s₀ + BitVec.ofNat 64 k) =
    if k < 512 * T then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (VG.Proof.ChaCha20Poly1305.AArch64.KS1 s₀).getD k 0
    else s.mem (dp s₀ + BitVec.ofNat 64 k)
  frame : Frame [sub s₀ 64 408, sub s₀ 32 16, dR s₀] s.mem u.mem
  mac : Repr u.mem (off (cx s₀) 448) key
    (msg ++ bytesAt (if enc then u.mem else s.mem) (dp s₀) (VG.Proof.ChaCha20Poly1305.AArch64.pre enc T))
  vec : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-! ## Helpers -/

/-- The vector registers other than `v8` and `v9` are kept. -/
theorem WP.otherV {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q)
    (hc : c.allInstrs VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV = true) :
    WP isa c s fun u => Q u ∧ ∀ r ∈ preservedV, r ≠ .v8 → r ≠ .v9 → u.v r = s.v r := by
  obtain ⟨t, u, he, hq⟩ := h
  exact ⟨t, u, he, hq, fun r hr h8 h9 => Exec.vec (fun i hi =>
    VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV_ne (List.all_eq_true.mp
      ((Code.allInstrs_eq _ c) ▸ hc) i hi) hr h8 h9) he⟩

theorem bulk_otherV (sve enc : Bool) :
    (Stitch.bulk sve enc).allInstrs VG.Proof.ChaCha20.AArch64.Rows6.keepsOtherV = true := by
  cases sve <;> cases enc
  · show Stitch.bulkOpen.allInstrs _ = true; lit_decide
  · show Stitch.bulkSeal.allInstrs _ = true; lit_decide
  · show Stitch.bulkOpenSve.allInstrs _ = true; lit_decide
  · show Stitch.bulkSealSve.allInstrs _ = true; lit_decide

/-- A byte of the data outside a frame of the context. -/
theorem data_frame {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (dR s₀).Disjoint r) {k : Nat} (hk : k < L s₀) :
    m' (dp s₀ + BitVec.ofNat 64 k) = m (dp s₀ + BitVec.ofNat 64 k) :=
  hf.bytes hd (Nat.le_of_lt (s₀.gpr .x5).isLt) hk

/-- The parts of the context `cryptStitched` writes, besides the stream's. -/
abbrev ctxW (s₀ : State) : List Region := [sub s₀ 64 408, sub s₀ 32 16]

theorem ctxW_data {s₀ : State} (hp : APre e s₀) : ∀ r ∈ VG.Proof.ChaCha20Poly1305.AArch64.ctxW s₀, (dR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact hp.c_d.symm.sub_right (sub_ctx s₀ (by lit_omega))

theorem ctxW_sub (s₀ : State) : ∀ r ∈ VG.Proof.ChaCha20Poly1305.AArch64.ctxW s₀, ∃ r' ∈ [workR s₀, dR s₀], Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩

theorem ctxW_saved (s₀ : State) : ∀ r ∈ VG.Proof.ChaCha20Poly1305.AArch64.ctxW s₀, (sub s₀ 576 56).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)

/-- The state after `cryptSetup`. -/
theorem setup_ok {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s) :
    WP isa (.block cryptSetup) s fun s₂ =>
      s₂.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s₂.gpr .x0 = off (cx s₀) 64 ∧
      s₂.gpr .x1 = dp s₀ ∧ s₂.gpr .x2 = s₀.gpr .x5 ∧ s₂.gpr .x3 = off (cx s₀) 128 ∧
      s₂.gpr .x5 = BitVec.ofNat 64 (if L s₀ < 512 then 1 else 0) ∧
      s₂.gpr .x22 = s.gpr .x22 ∧ s₂.gpr .x23 = s.gpr .x23 ∧
      Kept [sub s₀ 64 64] s s₂ ∧
      ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64 := by
  have core : WP isa (.block cryptSetup) s fun s₂ =>
      s₂.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32) ∧ s₂.gpr .x0 = off (cx s₀) 64 ∧
      s₂.gpr .x1 = dp s₀ ∧ s₂.gpr .x2 = s₀.gpr .x5 ∧ s₂.gpr .x3 = off (cx s₀) 128 ∧
      s₂.gpr .x5 = BitVec.ofNat 64 (if L s₀ < 512 then 1 else 0) ∧
      s₂.gpr .x22 = s.gpr .x22 ∧ s₂.gpr .x23 = s.gpr .x23 ∧ Kept [sub s₀ 64 64] s s₂ := by
    refine WP.block_append ((cryptA_ok hp h).mono fun s₁ ⟨m₁, x0₁, x1₁, x2₁, x3₁, k₁⟩ => ?_)
    refine (VG.Proof.ChaCha20.AArch64.Mixed8.check_ok s₁).mono
      fun s₂ ⟨x5₂, g₂, m₂, rd₂, wr₂, _, sp₂⟩ => ?_
    have k : Kept [sub s₀ 64 64] s s₂ :=
      ⟨fun r hr h30 => by
          rw [g₂ r (by intro e; subst e; exact absurd hr (by decide)), k₁.cs r hr h30],
        by rw [sp₂, k₁.sp], by rw [rd₂, k₁.rd], by rw [wr₂, k₁.wr], by rw [m₂]; exact k₁.frame⟩
    exact ⟨by rw [m₂, m₁], by rw [g₂ _ (by decide), x0₁], by rw [g₂ _ (by decide), x1₁],
      by rw [g₂ _ (by decide), x2₁], by rw [g₂ _ (by decide), x3₁], by rw [x5₂, x2₁],
      k.cs _ (pres .x22) (pres30 .x22), k.cs _ (pres .x23) (pres30 .x23), k⟩
  exact (WP.preservedV core (by lit_decide)).mono fun _ ⟨⟨a, b, c, d, e, f, g, i, k⟩, hv⟩ => ⟨a, b, c, d, e, f, g, i, k, hv⟩

/-- The ChaCha20 state after `cryptSetup`: counter 1. -/
theorem setup_cnt {s₀ : State} {s : State}
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀)) :
    stateAt (s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32)) (off (cx s₀) 64) =
      Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
  rw [show off (cx s₀) 112 = off (cx s₀) 64 + BitVec.ofNat 64 48 from (off_off _ 64 48).symm,
    VG.Proof.ChaCha20.AArch64.Xor.stateAt_writeW_counter, hst, set12_initState]

/-- Fewer than 512 bytes: no chunks. -/
theorem short_crypted (enc : Bool) {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hr : Repr s.mem (off (cx s₀) 448) key msg) {s₂ : State}
    (m₂ : s₂.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32))
    (x0₂ : s₂.gpr .x0 = off (cx s₀) 64) (x1₂ : s₂.gpr .x1 = dp s₀) (x2₂ : s₂.gpr .x2 = s₀.gpr .x5)
    (x3₂ : s₂.gpr .x3 = off (cx s₀) 128) (k₂ : Kept [sub s₀ 64 64] s s₂)
    (v₂ : ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) :
    VG.Proof.ChaCha20Poly1305.AArch64.Crypted enc s₀ s key msg 0 s₂ := by
  have i₂ := h.step1 k₂ (by lit_omega) (by lit_omega) (by lit_omega)
  have hd : ∀ r ∈ [sub s₀ 64 64], (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact hp.c_d.symm.sub_right (sub_ctx s₀ (by lit_omega))
  refine ⟨i₂.inv0, by omega, x0₂, ?_, ?_, x3₂, ?_, ?_, ?_, fun k hk => ?_, ?_, ?_, v₂⟩
  · rw [x1₂, Nat.mul_zero, Poly1305.AArch64.add_ofNat_zero]
  · rw [x2₂, Nat.mul_zero, Nat.sub_zero, hL]
  · rw [VG.Proof.ChaCha20Poly1305.AArch64.pre_zero, i₂.x22, Poly1305.AArch64.add_ofNat_zero]
  · rw [VG.Proof.ChaCha20Poly1305.AArch64.pre_zero, i₂.x23, Nat.sub_zero, hL]
  · rw [m₂, VG.Proof.ChaCha20Poly1305.AArch64.setup_cnt hst, Nat.mul_zero, VG.Proof.ChaCha20.ctr_zero]
  · rw [ite_eq_right (by omega)]; exact VG.Proof.ChaCha20Poly1305.AArch64.data_frame k₂.frame hd hk
  · exact k₂.frame.sub fun r hr => by
      rw [List.mem_singleton] at hr; rw [hr]
      exact ⟨sub s₀ 64 408, List.mem_cons_self, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
  · rw [VG.Proof.ChaCha20Poly1305.AArch64.pre_zero, Stitch.bytesAt_zero, List.append_nil]
    exact Repr.frame k₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) hr

/-! ## The accumulator in registers -/

theorem h2_le {a b c : Nat} (h : a + 2 ^ 64 * b + 2 ^ 128 * c < Spec.Poly1305.P) : c ≤ 4 := by
  have h₁ : 2 ^ 128 * c < 2 ^ 128 * 5 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) (Nat.lt_trans h (by decide))
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left h₁)

/-- The accumulator's words, from the 24 bytes. -/
theorem leNum_words (m : Mem) (c : Addr) :
    VG.Spec.Poly1305.leNum (bytesAt m (off c 448) 24) = (m.readW (off c 448) 64).toNat +
      2 ^ 64 * (m.readW (off c 456) 64).toNat + 2 ^ 128 * (m.readW (off c 464) 64).toNat := by
  rw [Poly1305.AArch64.leNum_acc]
  simp only [Poly1305.AArch64.w64, off, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The key's clamped words, as `polyIn` stores them. -/
theorem clamp_words (m : Mem) (c : Addr) :
    Poly1305.AArch64.Rk m (off c 448) = (m.readW (off c 472) 64 &&& VG.Proof.ChaCha20Poly1305.AArch64.M0).toNat +
      2 ^ 64 * (m.readW (off c 480) 64 &&& VG.Proof.ChaCha20Poly1305.AArch64.M1).toNat := by
  simp only [Poly1305.AArch64.Rk, Poly1305.AArch64.off, off, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem memIn_288 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (VG.Proof.ChaCha20Poly1305.AArch64.memIn m c a b).readW (off c 288) 64 = m.readW (off c 472) 64 &&& VG.Proof.ChaCha20Poly1305.AArch64.M0 := by
  rw [VG.Proof.ChaCha20Poly1305.AArch64.memIn, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    Mem.readW_writeW_self64]

theorem memIn_296 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (VG.Proof.ChaCha20Poly1305.AArch64.memIn m c a b).readW (off c 296) 64 = m.readW (off c 480) 64 &&& VG.Proof.ChaCha20Poly1305.AArch64.M1 := by
  rw [VG.Proof.ChaCha20Poly1305.AArch64.memIn, Mem.readW_writeW_self64]

theorem memIn_800 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (VG.Proof.ChaCha20Poly1305.AArch64.memIn m c a b).readW (off c 32) 64 = a := by
  rw [VG.Proof.ChaCha20Poly1305.AArch64.memIn, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self64]

theorem memIn_808 (m : Mem) (c : Addr) (a b : BitVec 64) :
    (VG.Proof.ChaCha20Poly1305.AArch64.memIn m c a b).readW (off c 40) 64 = b := by
  rw [VG.Proof.ChaCha20Poly1305.AArch64.memIn, readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega),
    readW64_off _ _ _ (by lit_omega) (by lit_omega) (by lit_omega), Mem.readW_writeW_self64]

/-- The words `polyIn` stores. -/
abbrev inR (s₀ : State) : List Region := [sub s₀ 288 16, sub s₀ 32 16]

theorem memIn_frame {s₀ : State} (m : Mem) (a b : BitVec 64) :
    Frame (VG.Proof.ChaCha20Poly1305.AArch64.inR s₀) m (VG.Proof.ChaCha20Poly1305.AArch64.memIn m (cx s₀) a b) := by
  have c (k d : Nat) (h₁ : k ≤ d) (h₂ : d + 8 ≤ k + 16) (h₃ : k + 16 ≤ 760) :
      (sub s₀ k 16).Contains (off (cx s₀) d) (64 / 8) :=
    contains_sub s₀ h₁ h₂ h₃
  exact ((((Frame.refl _ m).writeW (by simp) _ (c 32 32 (by decide) (by decide) (by decide))).writeW
    (by simp) _ (c 32 40 (by decide) (by decide) (by decide))).writeW (by simp) _
    (c 288 288 (by decide) (by decide) (by decide))).writeW (by simp) _
    (c 288 296 (by decide) (by decide) (by decide))

theorem storeHm_frame (m : Mem) (p : Addr) (w0 w1 w2 : BitVec 64) :
    Frame [⟨p, 24⟩] m (Poly1305.AArch64.storeHm m p w0 w1 w2) := by
  have c : ∀ d, d + 8 ≤ 24 → (Poly1305.AArch64.hR p).Contains (Poly1305.AArch64.off p d) (64 / 8) :=
    fun d hd => Poly1305.AArch64.hR_contains p hd
  exact (((Frame.refl _ m).writeW List.mem_cons_self _ (c 0 (by decide))).writeW List.mem_cons_self _
    (c 8 (by decide))).writeW List.mem_cons_self _ (c 16 (by decide))

/-- The pointer and length of the data not yet absorbed. -/
theorem restP_eq (enc : Bool) (d : Addr) {L T : Nat} (hT : 1 ≤ T) (hle : 512 * T ≤ L) :
    VG.Proof.ChaCha20Poly1305.AArch64.restP enc (d + BitVec.ofNat 64 (512 * T)) (BitVec.ofNat 64 (L - 512 * T)) =
      (d + BitVec.ofNat 64 (VG.Proof.ChaCha20Poly1305.AArch64.pre enc T), BitVec.ofNat 64 (L - VG.Proof.ChaCha20Poly1305.AArch64.pre enc T)) := by
  cases enc
  · rfl
  · simp only [VG.Proof.ChaCha20Poly1305.AArch64.restP, VG.Proof.ChaCha20Poly1305.AArch64.pre, ite_true]
    have e : 512 * T = 512 * (T - 1) + 512 := by omega
    refine Prod.ext ?_ ?_
    · show d + BitVec.ofNat 64 (512 * T) - BitVec.ofNat 64 512 = _
      rw [e, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_sub_cancel]
    · show BitVec.ofNat 64 (L - 512 * T) + BitVec.ofNat 64 512 = _
      rw [← BitVec.ofNat_add]; congr 1; omega

/-- The accumulator `polyIn` loads. -/
theorem acc_in {s₀ s₂ s₃ : State} {key msg : List Byte}
    (hr : Repr s₂.mem (off (cx s₀) 448) key msg) (x0₃ : s₃.gpr .x0 = off (cx s₀) 64)
    (a21 : s₃.gpr .x21 = s₂.mem.readW (off (cx s₀) 448) 64)
    (a22 : s₃.gpr .x22 = s₂.mem.readW (off (cx s₀) 456) 64)
    (a23 : s₃.gpr .x23 = s₂.mem.readW (off (cx s₀) 464) 64)
    {a b : BitVec 64} (m₃ : s₃.mem = VG.Proof.ChaCha20Poly1305.AArch64.memIn s₂.mem (cx s₀) a b) :
    Acc (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16)))
      (VG.Spec.Poly1305.accumulate (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16))) msg)
      s₃ := by
  have hA := hr.2.2
  rw [VG.Proof.ChaCha20Poly1305.AArch64.leNum_words] at hA
  have hlt := Poly1305.accumulate_lt (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16))) msg
  have r0 : Poly.rword s₃ VG.Impl.ChaCha20Poly1305.AArch64.Poly.r0Off =
      s₂.mem.readW (off (cx s₀) 472) 64 &&& VG.Proof.ChaCha20Poly1305.AArch64.M0 := by
    simp only [Poly.rword, VG.Impl.ChaCha20Poly1305.AArch64.Poly.r0Off, x0₃, m₃]
    rw [show off (cx s₀) 64 + BitVec.ofNat 64 224 = off (cx s₀) 288 from off_off _ 64 224, VG.Proof.ChaCha20Poly1305.AArch64.memIn_288]
  have r1 : Poly.rword s₃ VG.Impl.ChaCha20Poly1305.AArch64.Poly.r1Off =
      s₂.mem.readW (off (cx s₀) 480) 64 &&& VG.Proof.ChaCha20Poly1305.AArch64.M1 := by
    simp only [Poly.rword, VG.Impl.ChaCha20Poly1305.AArch64.Poly.r1Off, x0₃, m₃]
    rw [show off (cx s₀) 64 + BitVec.ofNat 64 232 = off (cx s₀) 296 from off_off _ 64 232, VG.Proof.ChaCha20Poly1305.AArch64.memIn_296]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Poly.hval, a21, a22, a23]; rw [hA]
  · rw [a23]; rw [← hA] at hlt; exact VG.Proof.ChaCha20Poly1305.AArch64.h2_le hlt
  · simp only [Poly.rval, r0, r1]
    rw [← VG.Proof.ChaCha20Poly1305.AArch64.clamp_words, ← Poly1305.AArch64.clamp_key, Poly1305.AArch64.off_24]
    exact congrArg (fun k => VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (List.take 16 k))) hr.2.1
  · rw [r0]; exact Poly1305.AArch64.Radix64.key0_lt _
  · rw [r1]; exact Poly1305.AArch64.Radix64.key1_lt _

/-! ## The chunks -/

theorem data_ctx {s₀ : State} (hp : APre e s₀) {k n : Nat} (h : k + n ≤ 760) :
    (dR s₀).Disjoint (sub s₀ k n) :=
  hp.c_d.symm.sub_right (sub_ctx s₀ h)

/-- A prefix of the data outside a frame of the context. -/
theorem prefix_frame {s₀ : State} {rs : List Region} {m m' : Mem} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (dR s₀).Disjoint r) {n : Nat} (hn : n ≤ L s₀) :
    bytesAt m' (dp s₀) n = bytesAt m (dp s₀) n :=
  bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hn))
    (Nat.le_trans hn (Nat.le_of_lt (s₀.gpr .x5).isLt))

/-- The saved `x27` and `x28` are outside the stream's regions. -/
theorem saved_bulk {s₀ : State} (hp : APre e s₀) {m m' : Mem} (hf : Frame (VG.Proof.ChaCha20Poly1305.AArch64.streamR s₀) m m') {d : Nat}
    (hd : d = 32 ∨ d = 40) : m'.readW (off (cx s₀) d) 64 = m.readW (off (cx s₀) d) 64 := by
  refine hf.readW (r := sub s₀ d 8) (Region.contains_self _ _) ?_ (by decide)
  have h₁ : d + 8 ≤ 760 := by omega
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_disj s₀ (by omega) h₁ (by lit_omega)
  · exact (VG.Proof.ChaCha20Poly1305.AArch64.data_ctx hp h₁).symm
  · exact sub_disj s₀ (by omega) h₁ (by lit_omega)

/-- At least 512 bytes: the chunks. -/
theorem long_crypted (enc : Bool) {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hr : Repr s.mem (off (cx s₀) 448) key msg) {s₂ : State}
    (m₂ : s₂.mem = s.mem.writeW (off (cx s₀) 112) (1 : BitVec 32))
    (x0₂ : s₂.gpr .x0 = off (cx s₀) 64) (x1₂ : s₂.gpr .x1 = dp s₀) (x2₂ : s₂.gpr .x2 = s₀.gpr .x5)
    (x3₂ : s₂.gpr .x3 = off (cx s₀) 128) (k₂ : Kept [sub s₀ 64 64] s s₂)
    (v₂ : ∀ r ∈ preservedV, (s₂.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64)
    (hL : 512 ≤ L s₀) :
    WP isa (.seq (.block polyIn) (.seq (Stitch.bulk sve enc) (.block (polyOut enc)))) s₂
      fun u => ∃ T, VG.Proof.ChaCha20Poly1305.AArch64.Crypted enc s₀ s key msg T u := by
  have hL' : L s₀ ≤ 2 ^ 64 := Nat.le_of_lt (s₀.gpr .x5).isLt
  have i₂ := h.step1 k₂ (by lit_omega) (by lit_omega) (by lit_omega)
  have hr₂ : Repr s₂.mem (off (cx s₀) 448) key msg := Repr.frame k₂.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)) hr
  refine WP.seq ((VG.Proof.ChaCha20Poly1305.AArch64.polyIn_ok hp i₂.x21 i₂.rd i₂.wr).mono
    fun s₃ ⟨⟨a21, a22, a23, m₃, g₃, rd₃, wr₃⟩, v₃, sp₃, _, _⟩ => ?_)
  have x0₃ : s₃.gpr .x0 = off (cx s₀) 64 := by rw [g₃ _ (by decide), x0₂]
  have x1₃ : s₃.gpr .x1 = dp s₀ := by rw [g₃ _ (by decide), x1₂]
  have x2₃ : s₃.gpr .x2 = s₀.gpr .x5 := by rw [g₃ _ (by decide), x2₂]
  have x3₃ : s₃.gpr .x3 = off (cx s₀) 128 := by rw [g₃ _ (by decide), x3₂]
  have ha := VG.Proof.ChaCha20Poly1305.AArch64.acc_in hr₂ x0₃ a21 a22 a23 m₃
  refine WP.seq ((WP.otherV (VG.Proof.ChaCha20Poly1305.AArch64.bulkA_ok enc hp x0₃ x1₃ x2₃ x3₃ hL (by rw [wr₃, i₂.wr]) ha)
    (VG.Proof.ChaCha20Poly1305.AArch64.bulk_otherV sve enc)).mono fun s₄ ⟨⟨⟨T, hB⟩, rd₄, wr₄, sp₄, f₄⟩, ov₄⟩ => ?_)
  have hi := hB.inv
  have x0₄ : s₄.gpr .x0 = off (cx s₀) 64 := by
    have e := hi.x0; simp only [State.withRegions_gpr, Stitch.st_rebase,
      VG.Proof.ChaCha20.AArch64.Xor.st, x0₃] at e; exact e
  have x1₄ : s₄.gpr .x1 = dp s₀ + BitVec.ofNat 64 (512 * T) := by
    have e := hi.x1; simp only [State.withRegions_gpr, Stitch.dp_rebase,
      VG.Proof.ChaCha20.AArch64.Xor.dp, x1₃] at e; exact e
  have hLB : VG.Proof.ChaCha20.AArch64.Xor.L (s₃.withRegions [] (VG.Proof.ChaCha20Poly1305.AArch64.streamR s₀)) = L s₀ := by
    simp only [VG.Proof.ChaCha20.AArch64.Xor.L, State.withRegions_gpr, x2₃]
  have x2₄ : s₄.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * T) := by
    have e := hi.x2; simp only [State.withRegions_gpr, Stitch.L_rebase, hLB] at e; exact e
  have x3₄ : s₄.gpr .x3 = off (cx s₀) 128 := by
    have e := hi.x3; simp only [State.withRegions_gpr, Stitch.bp_rebase,
      VG.Proof.ChaCha20.AArch64.Xor.bp, x3₃] at e; exact e
  have le₄ : 512 * T ≤ L s₀ := by have e := hi.le; simp only [Stitch.L_rebase, hLB] at e; exact e
  refine (VG.Proof.ChaCha20Poly1305.AArch64.polyOut_ok hp enc x0₄ (by rw [rd₄, rd₃, i₂.rd]) (by rw [wr₄, wr₃, i₂.wr])).mono
    fun s₅ ⟨⟨hv₅, m₅, x21₅, x27₅, x28₅, x22₅, x23₅, g₅, rd₅, wr₅⟩, vv₅, sp₅, _, _⟩ => ⟨T, ?_⟩
  -- Memory.
  have f₂₃ : Frame (VG.Proof.ChaCha20Poly1305.AArch64.inR s₀) s₂.mem s₃.mem := by rw [m₃]; exact VG.Proof.ChaCha20Poly1305.AArch64.memIn_frame _ _ _
  have f₄₅ : Frame [sub s₀ 448 24] s₄.mem s₅.mem := by rw [m₅]; exact VG.Proof.ChaCha20Poly1305.AArch64.storeHm_frame _ _ _ _ _
  have hF : Frame [sub s₀ 64 408, sub s₀ 32 16, dR s₀] s.mem s₅.mem := by
    have e (r : Region) (k n : Nat) (h₁ : 64 ≤ k) (h₂ : k + n ≤ 472) (hr : r = sub s₀ k n) :
        ∃ r' ∈ [sub s₀ 64 408, sub s₀ 32 16, dR s₀], Region.Sub r r' :=
      ⟨sub s₀ 64 408, List.mem_cons_self, hr ▸ sub_sub s₀ h₁ (by lit_omega) (by lit_omega)⟩
    refine ((k₂.frame.sub ?_).trans (f₂₃.sub ?_)).trans ((f₄.sub ?_).trans (f₄₅.sub ?_)) <;>
      intro r hr <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    · exact e r 64 64 (by decide) (by decide) hr
    · rcases hr with hr | hr
      · exact e r 288 16 (by decide) (by decide) hr
      · exact ⟨sub s₀ 32 16, by simp, hr ▸ fun _ h => h⟩
    · rcases hr with hr | hr | hr
      · exact e r 64 64 (by decide) (by decide) hr
      · exact ⟨dR s₀, by simp, hr ▸ fun _ h => h⟩
      · exact e r 128 320 (by decide) (by decide) hr
    · exact e r 448 24 (by decide) (by decide) hr
  have d₀₃ (k : Nat) (hk : k < L s₀) :
      s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := by
    rw [VG.Proof.ChaCha20Poly1305.AArch64.data_frame f₂₃ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact VG.Proof.ChaCha20Poly1305.AArch64.data_ctx hp (by lit_omega)) hk,
      VG.Proof.ChaCha20Poly1305.AArch64.data_frame k₂.frame (by
        intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.ChaCha20Poly1305.AArch64.data_ctx hp (by lit_omega)) hk]
  have st₃ : stateAt s₃.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 1 (N s₀) := by
    rw [stateAt_frame f₂₃ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)),
      m₂, VG.Proof.ChaCha20Poly1305.AArch64.setup_cnt hst]
  -- The data and the counter.
  have data₅ : ∀ k < L s₀, s₅.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < 512 * T then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (VG.Proof.ChaCha20Poly1305.AArch64.KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k) := by
    intro k hk
    have e := hi.data k (by rw [Stitch.L_rebase, hLB]; exact hk)
    simp only [Stitch.dp_rebase, Stitch.D0_rebase, Stitch.KS_rebase] at e
    simp only [State.withRegions_mem, VG.Proof.ChaCha20.AArch64.Xor.D0, VG.Proof.ChaCha20.AArch64.Xor.KS,
      VG.Proof.ChaCha20.AArch64.Xor.S0, VG.Proof.ChaCha20.AArch64.Xor.dp,
      VG.Proof.ChaCha20.AArch64.Xor.st, State.withRegions_gpr, x0₃, x1₃, hLB, st₃, d₀₃ k hk] at e
    rw [VG.Proof.ChaCha20Poly1305.AArch64.data_frame f₄₅ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.ChaCha20Poly1305.AArch64.data_ctx hp (by lit_omega)) hk, e]
  have hd₄₅ : ∀ r ∈ [sub s₀ 448 24], (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.ChaCha20Poly1305.AArch64.data_ctx hp (by lit_omega)
  have hd₂₃ : ∀ r ∈ VG.Proof.ChaCha20Poly1305.AArch64.inR s₀, (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact VG.Proof.ChaCha20Poly1305.AArch64.data_ctx hp (by lit_omega)
  have hd₂ : ∀ r ∈ [sub s₀ 64 64], (dR s₀).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.ChaCha20Poly1305.AArch64.data_ctx hp (by lit_omega)
  have cnt₅ : stateAt s₅.mem (off (cx s₀) 64) =
      ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (8 * T) := by
    have e := hi.cnt
    simp only [Stitch.st_rebase, Stitch.S0_rebase] at e
    simp only [State.withRegions_mem, VG.Proof.ChaCha20.AArch64.Xor.S0,
      VG.Proof.ChaCha20.AArch64.Xor.st, State.withRegions_gpr, x0₃, st₃] at e
    rw [stateAt_frame f₄₅ (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)), e]
  have r₄ (d : Nat) (hd : d = 32 ∨ d = 40) :
      s₄.mem.readW (off (cx s₀) d) 64 = s₃.mem.readW (off (cx s₀) d) 64 := VG.Proof.ChaCha20Poly1305.AArch64.saved_bulk hp f₄ hd
  have un₅ : ∀ r ∈ untouched, s₅.gpr r = s₀.gpr r := by
    intro r hr
    simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
    have via (r : Reg) (hc : r ∈ preserved) (hn : r ∉ Stitch.accRegs)
        (h5 : r ∉ [Reg.x4, .x5, .x6, .x9, .x10, .x11, .x12, .x13, .x14, .x21, .x22, .x23, .x27, .x28])
        (h3 : r ∉ [Reg.x21, .x22, .x23, .x24, .x25]) (hu : r ∈ untouched) :
        s₅.gpr r = s₀.gpr r := by
      have e := hB.cs r hc
      simp only [State.withRegions_gpr] at e
      rw [g₅ r h5, e, rebase_of hn, State.withRegions_gpr, g₃ r h3,
        k₂.cs r hc (untouched_preserved r hu).2, h.un r hu]
    have x2728 (r : Reg) (d : Nat) (hd : d = 32 ∨ d = 40) (hu : r ∈ untouched)
        (hx : s₅.gpr r = s₄.mem.readW (off (cx s₀) d) 64)
        (hm : (VG.Proof.ChaCha20Poly1305.AArch64.memIn s₂.mem (cx s₀) (s₂.gpr .x27) (s₂.gpr .x28)).readW (off (cx s₀) d) 64 = s₂.gpr r) :
        s₅.gpr r = s₀.gpr r := by
      rw [hx, r₄ d hd, m₃, hm, k₂.cs r (untouched_preserved r hu).1 (untouched_preserved r hu).2,
        h.un r hu]
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact via _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · exact x2728 _ 32 (.inl rfl) (by decide) x27₅ (VG.Proof.ChaCha20Poly1305.AArch64.memIn_800 _ _ _ _)
    · exact x2728 _ 40 (.inr rfl) (by decide) x28₅ (VG.Proof.ChaCha20Poly1305.AArch64.memIn_808 _ _ _ _)
  have hlt := Poly1305.accumulate_lt (VG.Spec.Poly1305.clamp (VG.Spec.Poly1305.leNum (key.take 16))) msg
  have ac₄ := hB.acc
  have hX := hv₅ ac₄.h2
  rw [show VG.Proof.ChaCha20Poly1305.AArch64.hacc s₄ = Poly.hval (s₄.withRegions [] (VG.Proof.ChaCha20Poly1305.AArch64.streamR s₀)) from rfl, ac₄.h,
    Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _)] at hX
  have k24 : (off (cx s₀) 448 + 24 : Addr) = off (cx s₀) 472 := off_off _ 448 24
  have hr1 := hr.2.1
  rw [k24] at hr1
  refine ⟨⟨x21₅, un₅, by rw [sp₅, sp₄, sp₃, k₂.sp, h.sp], by rw [rd₅, rd₄, rd₃, i₂.rd],
      by rw [wr₅, wr₄, wr₃, i₂.wr], h.saved.frame hF ?_, h.frame.trans (hF.sub ?_)⟩,
    le₄, by rw [g₅ _ (by decide), x0₄], by rw [g₅ _ (by decide), x1₄], by rw [g₅ _ (by decide), x2₄],
    by rw [g₅ _ (by decide), x3₄], by rw [x22₅, x1₄, x2₄, VG.Proof.ChaCha20Poly1305.AArch64.restP_eq enc _ hB.pos le₄],
    by rw [x23₅, x1₄, x2₄, VG.Proof.ChaCha20Poly1305.AArch64.restP_eq enc _ hB.pos le₄], cnt₅, data₅, hF, ⟨?_, ?_, ?_⟩, fun r hr => ?_⟩
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
    · exact hp.c_d.sub_left (sub_ctx s₀ (by lit_omega))
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨workR s₀, by simp, sub1 s₀ (by lit_omega) (by lit_omega)⟩
    · exact ⟨dR s₀, by simp, fun _ h => h⟩
  · rw [List.length_append, Poly1305.length_bytesAt]
    have := hr.1; have := VG.Proof.ChaCha20Poly1305.AArch64.pre_mod enc T; omega
  · rw [k24, bytesAt_frame hF (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact sub_disj s₀ (by lit_omega) (by lit_omega) (by lit_omega)
      · exact (VG.Proof.ChaCha20Poly1305.AArch64.data_ctx hp (by lit_omega)).symm) (by lit_omega)]
    exact hr1
  · rw [m₅, Poly1305.AArch64.storeHm_acc, ← m₅]
    show Poly1305.AArch64.Radix64.hval s₅ = _
    rw [hX, Poly1305.accumulate_append hr.1]
    refine congrArg (absorbAll _ _) ?_
    cases enc
    · simp only [Bool.false_eq_true, ite_false, VG.Proof.ChaCha20Poly1305.AArch64.pre, State.withRegions_mem,
        VG.Proof.ChaCha20.AArch64.Xor.dp, State.withRegions_gpr, x1₃]
      rw [VG.Proof.ChaCha20Poly1305.AArch64.prefix_frame f₂₃ hd₂₃ le₄, VG.Proof.ChaCha20Poly1305.AArch64.prefix_frame k₂.frame hd₂ le₄]
    · simp only [ite_true, VG.Proof.ChaCha20Poly1305.AArch64.pre, State.withRegions_mem, VG.Proof.ChaCha20.AArch64.Xor.dp,
        State.withRegions_gpr, x1₃]
      rw [VG.Proof.ChaCha20Poly1305.AArch64.prefix_frame f₄₅ hd₄₅ (by omega)]
  · have e4 : s₄.v r = s₃.v r := by
      by_cases h8 : r = .v8
      · subst h8; simpa using hB.v8
      by_cases h9 : r = .v9
      · subst h9; simpa using hB.v9
      exact ov₄ r hr h8 h9
    rw [vv₅, e4, v₃]; exact v₂ r hr

theorem cryptStitched_ok (enc : Bool) {s₀ : State} (hp : APre e s₀) {s : State} (h : Inv s₀ s)
    (hst : stateAt s.mem (off (cx s₀) 64) = Spec.ChaCha20.initState (K s₀) 0 (N s₀))
    {key msg : List Byte} (hr : Repr s.mem (off (cx s₀) 448) key msg) :
    WP isa (cryptStitched sve enc) s fun u => ∃ T, VG.Proof.ChaCha20Poly1305.AArch64.Crypted enc s₀ s key msg T u := by
  unfold cryptStitched
  refine WP.seq ((VG.Proof.ChaCha20Poly1305.AArch64.setup_ok hp h).mono fun s₂ ⟨m₂, x0₂, x1₂, x2₂, x3₂, x5₂, _, _, k₂, v₂⟩ => ?_)
  apply WP.ite (decide (L s₀ < 512)) (VG.Proof.ChaCha20.AArch64.Mixed8.nonzero_short x5₂)
  · intro _
    exact WP.block_nil ⟨0, VG.Proof.ChaCha20Poly1305.AArch64.short_crypted enc hp h hst hr m₂ x0₂ x1₂ x2₂ x3₂ k₂ v₂⟩
  · intro hs
    exact VG.Proof.ChaCha20Poly1305.AArch64.long_crypted enc hp h hst hr m₂ x0₂ x1₂ x2₂ x3₂ k₂ v₂
      (by have := of_decide_eq_false hs; omega)

end VG.Proof.ChaCha20Poly1305.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Stitched.Rest`. -/
section

/-!
# ChaCha20-Poly1305 on AArch64, stitched: the rest of the data

`vg_chacha20_xor` (any backend) on the data after the chunks, from the
counter after them: the whole data encrypted from counter 1.
-/

namespace VG.Proof.ChaCha20Poly1305.AArch64

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Impl.ChaCha20.AArch64.Xor (mov)
open VG.Proof.ChaCha20.AArch64.Xor (wp_addImm wp_mov)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.Poly1305 (bytesAt)
open VG.Spec.ChaCha20 (stateAt keystream)

variable {e : Bool}

/-- The data after the chunks. -/
abbrev restR (s₀ : State) (T : Nat) : Region :=
  ⟨dp s₀ + BitVec.ofNat 64 (512 * T), L s₀ - 512 * T⟩

theorem data_in {s₀ : State} {k : Nat} (hk : k < L s₀) :
    (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
  Offset.contains_base _ (by omega) (by have h : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt; omega)

theorem not_rest {s₀ : State} {T k : Nat} (hk : k < 512 * T) (hT : 512 * T ≤ L s₀) :
    ¬ (VG.Proof.ChaCha20Poly1305.AArch64.restR s₀ T).Contains (dp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega) (by omega)]
  split <;> omega

/-- The data from `512 T`, encrypted from the counter after `8 T` blocks. -/
theorem rest_call (v : Proof.ChaCha20.AArch64.XorImpl) {s₀ : State} (hp : APre e s₀) {s w : State}
    {T : Nat} (hle : 512 * T ≤ L s₀)
    (hx0 : w.gpr .x0 = off (cx s₀) 64) (hx1 : w.gpr .x1 = dp s₀ + BitVec.ofNat 64 (512 * T))
    (hx2 : w.gpr .x2 = BitVec.ofNat 64 (L s₀ - 512 * T)) (hx3 : w.gpr .x3 = off (cx s₀) 128)
    (hwr : w.wr = s₀.wr)
    (hcnt : stateAt w.mem (off (cx s₀) 64) = ctr (Spec.ChaCha20.initState (K s₀) 1 (N s₀)) (8 * T))
    (hdata : ∀ k < L s₀, w.mem (dp s₀ + BitVec.ofNat 64 k) =
      if k < 512 * T then s.mem (dp s₀ + BitVec.ofNat 64 k) ^^^ (VG.Proof.ChaCha20Poly1305.AArch64.KS1 s₀).getD k 0
      else s.mem (dp s₀ + BitVec.ofNat 64 k)) :
    WP isa (.call v.callee.name v.callee.code) w fun s' =>
      (∀ r ∈ preservedV, (s'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64) ∧
      Kept [sub s₀ 64 384, dR s₀] w s' ∧ Frame [sub s₀ 64 384, VG.Proof.ChaCha20Poly1305.AArch64.restR s₀ T] w.mem s'.mem ∧
      bytesAt s'.mem (dp s₀) (L s₀) =
        Spec.ChaCha20.encrypt (K s₀) 1 (N s₀) (bytesAt s.mem (dp s₀) (L s₀)) := by
  have hL : L s₀ < 2 ^ 64 := (s₀.gpr .x5).isLt
  have ts : Region.Sub (VG.Proof.ChaCha20Poly1305.AArch64.restR s₀ T) (dR s₀) := Offset.sub_base _ (by omega)
  have hw : Covers [⟨off (cx s₀) 64, 64⟩, VG.Proof.ChaCha20Poly1305.AArch64.restR s₀ T, ⟨off (cx s₀) 128, 320⟩] w.wr := by
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨ctxR s₀, by rw [hwr]; first | exact hp.ctx_wr | exact hp.d_wr, 64, rfl, by show 64 + 64 ≤ 760; omega⟩
    · exact ⟨dR s₀, by rw [hwr]; first | exact hp.ctx_wr | exact hp.d_wr, 512 * T, rfl, by show 512 * T + (L s₀ - 512 * T) ≤ L s₀; omega⟩
    · exact ⟨ctxR s₀, by rw [hwr]; first | exact hp.ctx_wr | exact hp.d_wr, 128, rfl, by show 128 + 320 ≤ 760; omega⟩
  refine xor_call v hx0 hx1 hx2 hx3 (by omega)
    ((hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega))).sub_right ts)
    (sub_disj s₀ (a := 64) (n := 64) (b := 128) (m := 320) (by lit_omega) (by lit_omega) (by lit_omega))
    ((hp.c_d.symm.sub_right (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega))).sub_left ts)
    (by have := hp.wrap_d; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
    (Covers.right hw) hw fun s' v' k' d' => ?_
  refine ⟨v', ?_, ?_, ?_⟩
  · refine k'.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨dR s₀, by simp, ts⟩
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  · refine k'.frame.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (Nat.le_refl _) (by lit_omega) (by lit_omega)⟩
    · exact ⟨VG.Proof.ChaCha20Poly1305.AArch64.restR s₀ T, by simp, fun _ h => h⟩
    · exact ⟨sub s₀ 64 384, by simp, sub_sub s₀ (by lit_omega) (by lit_omega) (by lit_omega)⟩
  · show Spec.ChaCha20.bytesAt _ _ _ = Spec.ChaCha20.encrypt _ _ _ (Spec.ChaCha20.bytesAt _ _ _)
    rw [encrypt_eq, show (Spec.ChaCha20.bytesAt s.mem (dp s₀) (L s₀)).length = L s₀ from
      VG.Proof.Poly1305.length_bytesAt _ _ _]
    refine VG.Proof.ChaCha20.bytesAt_xor (VG.Proof.ChaCha20.length_keystream _ _) fun k hk => ?_
    by_cases hk' : k < 512 * T
    · have hs : ¬ (⟨off (cx s₀) 64, 64⟩ : Region).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 64) (by lit_omega)) _ hh (VG.Proof.ChaCha20Poly1305.AArch64.data_in hk)
      have hb : ¬ (⟨off (cx s₀) 128, 320⟩ : Region).Contains (dp s₀ + BitVec.ofNat 64 k) 1 :=
        fun hh => hp.c_d.sub_left (sub_ctx s₀ (k := 128) (n := 320) (by lit_omega)) _ hh (VG.Proof.ChaCha20Poly1305.AArch64.data_in hk)
      rw [k'.frame _ (by
        intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hs
        · exact VG.Proof.ChaCha20Poly1305.AArch64.not_rest hk' hle
        · exact hb), hdata k hk, ite_eq_left hk']
    · have ea : dp s₀ + BitVec.ofNat 64 (512 * T) + BitVec.ofNat 64 (k - 512 * T) =
          dp s₀ + BitVec.ofNat 64 k := by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' (by omega)]
      have x := VG.Proof.ChaCha20.AArch64.Mixed8.bytes_of_bytesAt
        (VG.Proof.ChaCha20.length_keystream _ _) d' (k := k - 512 * T) (by omega)
      rw [ea, hdata k hk, ite_eq_right hk', hcnt,
        VG.Proof.ChaCha20.keystream_getD _ (by omega)] at x
      rw [x, VG.Proof.ChaCha20.AArch64.Mixed8.ks_shift _ hk (t := T) (by omega)]

/-- The data before the rest is kept. -/
theorem prefix_rest {s₀ : State} (hp : APre e s₀) {m m' : Mem} {T n : Nat}
    (hf : Frame [sub s₀ 64 384, VG.Proof.ChaCha20Poly1305.AArch64.restR s₀ T] m m') (hn : n ≤ 512 * T) (hT : 512 * T ≤ L s₀) :
    bytesAt m' (dp s₀) n = bytesAt m (dp s₀) n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  refine hf _ fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact fun hh => hp.c_d.sub_left (sub_ctx s₀ (k := 64) (n := 384) (by lit_omega)) _ hh
      (VG.Proof.ChaCha20Poly1305.AArch64.data_in (by omega))
  · exact VG.Proof.ChaCha20Poly1305.AArch64.not_rest (by omega) hT

/-- `cryptRest`'s arguments: the stream's, from the context and `x22`, `x23`. -/
theorem restArgs_ok {s₀ : State} {w : State} (hx21 : w.gpr .x21 = cx s₀) :
    WP isa (.block [.addImm .x .x0 .x21 64, mov .x1 .x22, mov .x2 .x23, .addImm .x .x3 .x21 128]) w
      fun w' => (w'.gpr .x0 = off (cx s₀) 64 ∧ w'.gpr .x1 = w.gpr .x22 ∧ w'.gpr .x2 = w.gpr .x23 ∧
        w'.gpr .x3 = off (cx s₀) 128 ∧ Kept [] w w') ∧
        ∀ r ∈ preservedV, (w'.v r).extractLsb' 0 64 = (w.v r).extractLsb' 0 64 := by
  have core : WP isa (.block [.addImm .x .x0 .x21 64, mov .x1 .x22, mov .x2 .x23,
      .addImm .x .x3 .x21 128]) w fun w' =>
      w'.gpr .x0 = off (cx s₀) 64 ∧ w'.gpr .x1 = w.gpr .x22 ∧ w'.gpr .x2 = w.gpr .x23 ∧
      w'.gpr .x3 = off (cx s₀) 128 ∧ w'.mem = w.mem ∧ w'.rd = w.rd ∧ w'.wr = w.wr :=
    wp_addImm (by decide) fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ =>
      wp_addImm (by decide) fun s₄ u₄ => WP.block_nil
        ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hx21],
          by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)],
          by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide)],
          by rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hx21],
          by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
          by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
  refine WP.preservedV (WP.mono (WP.kept core (by simp [mov, dstOf, preserved]))
    fun w' ⟨⟨h0, h1, h2, h3, hm, hrd, hwr⟩, hg, hsp⟩ =>
      ⟨h0, h1, h2, h3, Kept.of hg hsp hrd hwr (by rw [hm]; exact Frame.refl _ _)⟩) (by lit_decide)

end VG.Proof.ChaCha20Poly1305.AArch64

end
