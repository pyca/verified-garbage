import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.ChaCha20.StreamBytes
import VerifiedGarbage.Impl.ChaCha20.X86
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Impl.ChaCha20.X86.Xor
import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.ChaCha20.X86.Lit

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86.Block`. -/
section

section

/-!
# ChaCha20 block function on x86 (32-bit): the rounds
-/

namespace VG.Proof.ChaCha20.X86

open VG VG.X86 VG.Impl.ChaCha20.X86 VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)

/-- The address of word `k` of `buf`, relative to its 64-bit address `B`. -/
abbrev wordAddr (B : Addr) (k : Nat) : Addr := B + BitVec.ofNat 64 (4 * k)

/-- The state `v` is in `buf[0..64)`. -/
def Holds (B : Addr) (v : CState) (m : Mem) : Prop :=
  ∀ k (hk : k < 16), m.readW (VG.Proof.ChaCha20.X86.wordAddr B k) 32 = v[k]

theorem word_sep (B : Addr) {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    Mem.Sep (VG.Proof.ChaCha20.X86.wordAddr B j) 4 (VG.Proof.ChaCha20.X86.wordAddr B k) 4 := Offset.sep B (by lit_omega) (by lit_omega) (by lit_omega)

theorem readW_writeW_word (m : Mem) (B : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) : (m.writeW (VG.Proof.ChaCha20.X86.wordAddr B k) v).readW (VG.Proof.ChaCha20.X86.wordAddr B j) 32 = m.readW (VG.Proof.ChaCha20.X86.wordAddr B j) 32 :=
  Mem.readW_writeW_sep (VG.Proof.ChaCha20.X86.word_sep B hj hk h) (by decide)

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- The working state, `buf[0..64)`. -/
abbrev workR (B : Addr) : Region := ⟨B, 64⟩

theorem word_in_work (B : Addr) {k : Nat} (hk : k < 16) : (VG.Proof.ChaCha20.X86.workR B).Contains (VG.Proof.ChaCha20.X86.wordAddr B k) 4 := Offset.contains_base B (by lit_omega) (by lit_omega)

/-- What the rounds need of the machine state: `esi` points to `buf`, whose
working state is readable and writable. -/
structure Ctx (B : Addr) (s : State) : Prop where
  ea : ∀ k < 16, addr (s.gpr .esi) (4 * k) = VG.Proof.ChaCha20.X86.wordAddr B k
  inw : ∀ k < 16, InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.X86.wordAddr B k) 4
  outw : ∀ k < 16, InRegions s.wr (VG.Proof.ChaCha20.X86.wordAddr B k) 4

/-! ## One quarter round -/

theorem qr_ok (s : State) (va vb vc vd : Word)
    (ha : s.gpr .eax = va) (hb : s.gpr .ebx = vb) (hc : s.gpr .ecx = vc) (hd : s.gpr .edx = vd) :
    WP isa (.block qr) s fun s' =>
      s'.gpr .eax = (quarterRound va vb vc vd).1 ∧ s'.gpr .ebx = (quarterRound va vb vc vd).2.1 ∧
      s'.gpr .ecx = (quarterRound va vb vc vd).2.2.1 ∧ s'.gpr .edx = (quarterRound va vb vc vd).2.2.2 ∧
      s'.gpr .esi = s.gpr .esi ∧ s'.gpr .edi = s.gpr .edi ∧ s'.gpr .esp = s.gpr .esp ∧
      s'.gpr .ebp = s.gpr .ebp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, Nat.reducePow, and_self, qr, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift, readSrc,
    State.setReg, arithFlags, State.setFlags, ha, hb, hc, hd,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  and_intros
  all_goals simp only [quarterRound_eq]

theorem quarter_ok {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hd : [x, y, z, w].Nodup) {B : Addr} {v : CState} {s : State} (hctx : VG.Proof.ChaCha20.X86.Ctx B s)
    (h : VG.Proof.ChaCha20.X86.Holds B v s.mem) :
    WP isa (quarter x y z w) s fun s' =>
      VG.Proof.ChaCha20.X86.Holds B (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s'.mem ∧ Frame [VG.Proof.ChaCha20.X86.workR B] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .esi = s.gpr .esi ∧ s'.gpr .edi = s.gpr .edi ∧
      s'.gpr .esp = s.gpr .esp ∧ s'.gpr .ebp = s.gpr .ebp := by
  have nd : (x ≠ y ∧ x ≠ z ∧ x ≠ w) ∧ (y ≠ z ∧ y ≠ w) ∧ z ≠ w := by simpa using hd
  obtain ⟨⟨nxy, nxz, nxw⟩, ⟨nyz, nyw⟩, nzw⟩ := nd
  have ex := hctx.ea x hx; have ey := hctx.ea y hy; have ez := hctx.ea z hz; have ew := hctx.ea w hw
  have ix := hctx.inw x hx; have iy := hctx.inw y hy; have iz := hctx.inw z hz; have iw := hctx.inw w hw
  have ox := hctx.outw x hx; have oy := hctx.outw y hy; have oz := hctx.outw z hz
  have ow := hctx.outw w hw
  simp only [addr] at ex ey ez ew
  unfold quarter
  rw [WP.block_append_iff, WP.block_append_iff]
  -- The loads.
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg, State.ea,
    at_, State.load32, ex, ey, ez, ew, ix, iy, iz, iw, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine WP.mono (VG.Proof.ChaCha20.X86.qr_ok _ (v[x]'hx) (v[y]'hy) (v[z]'hz) (v[w]'hw) (by simp [h x hx]) (by simp [h y hy])
    (by simp [h z hz]) (by simp [h w hw])) fun s₁ ⟨ha, hb, hc, hd,
    hesi, hedi, hesp, hebp, hm, hrd, hwr⟩ => ?_
  simp only [ite_false, reduceCtorEq] at hesi hedi hesp hebp
  -- The stores.
  apply WP.of_runBlock
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, State.ea, State.store32, hesi,
    ex, ey, ez, ew, hrd, hwr, hm, ox, oy, oz, ow, Option.some.injEq,
    exists_eq_left', ha, hb, hc, hd]
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left 2
  all_goals try first | trivial | exact hedi | exact hesp | exact hebp
  · rw [qround_get _ _ _ _ _ k hk]
    simp only
    have g : ∀ j (hj : j < 16), s.mem.readW (VG.Proof.ChaCha20.X86.wordAddr B j) 32 = v[j] := h
    by_cases e4 : w = k
    · subst e4; simp only [ite_true]
      rw [Mem.readW_writeW_self32]; rfl
    by_cases e3 : z = k
    · subst e3; simp only [ite_true, e4, ite_false]
      rw [VG.Proof.ChaCha20.X86.readW_writeW_word _ _ _ hz hw nzw, Mem.readW_writeW_self32]; rfl
    by_cases e2 : y = k
    · subst e2; simp only [ite_true, e4, e3, ite_false]
      rw [VG.Proof.ChaCha20.X86.readW_writeW_word _ _ _ hy hw nyw, VG.Proof.ChaCha20.X86.readW_writeW_word _ _ _ hy hz nyz,
        Mem.readW_writeW_self32]; rfl
    by_cases e1 : x = k
    · subst e1; simp only [ite_true, e4, e3, e2, ite_false]
      rw [VG.Proof.ChaCha20.X86.readW_writeW_word _ _ _ hx hw nxw, VG.Proof.ChaCha20.X86.readW_writeW_word _ _ _ hx hz nxz,
        VG.Proof.ChaCha20.X86.readW_writeW_word _ _ _ hx hy nxy, Mem.readW_writeW_self32]; rfl
    simp only [e4, e3, e2, e1, ite_false]
    rw [VG.Proof.ChaCha20.X86.readW_writeW_word _ _ _ hk hw (Ne.symm e4), VG.Proof.ChaCha20.X86.readW_writeW_word _ _ _ hk hz (Ne.symm e3),
      VG.Proof.ChaCha20.X86.readW_writeW_word _ _ _ hk hy (Ne.symm e2), VG.Proof.ChaCha20.X86.readW_writeW_word _ _ _ hk hx (Ne.symm e1)]
    exact g k hk
  · exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.ChaCha20.X86.word_in_work B hx)).writeW
      (List.mem_singleton_self _) _ (VG.Proof.ChaCha20.X86.word_in_work B hy)).writeW (List.mem_singleton_self _) _
      (VG.Proof.ChaCha20.X86.word_in_work B hz)).writeW (List.mem_singleton_self _) _ (VG.Proof.ChaCha20.X86.word_in_work B hw)

/-! ## Double rounds -/

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (B : Addr) (v : CState) (s₀ s : State) : Prop where
  holds : VG.Proof.ChaCha20.X86.Holds B v s.mem
  frame : Frame [VG.Proof.ChaCha20.X86.workR B] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esi : s.gpr .esi = s₀.gpr .esi
  edi : s.gpr .edi = s₀.gpr .edi
  esp : s.gpr .esp = s₀.gpr .esp
  ebp : s.gpr .ebp = s₀.gpr .ebp

theorem RI.ctx {B : Addr} {v : CState} {s₀ s : State} (h : VG.Proof.ChaCha20.X86.RI B v s₀ s) (hc : VG.Proof.ChaCha20.X86.Ctx B s₀) :
    VG.Proof.ChaCha20.X86.Ctx B s :=
  ⟨fun k hk => by rw [h.esi]; exact hc.ea k hk, fun k hk => by rw [h.rd, h.wr]; exact hc.inw k hk,
    fun k hk => by rw [h.wr]; exact hc.outw k hk⟩

theorem quarter_step {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hd : [x, y, z, w].Nodup) {B : Addr} {v : CState} {s₀ s : State} (hctx : VG.Proof.ChaCha20.X86.Ctx B s₀)
    (h : VG.Proof.ChaCha20.X86.RI B v s₀ s) :
    WP isa (quarter x y z w) s (VG.Proof.ChaCha20.X86.RI B (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) :=
  WP.mono (VG.Proof.ChaCha20.X86.quarter_ok hx hy hz hw hd (h.ctx hctx) h.holds)
    fun _ ⟨hh, hf, hrd, hwr, hesi, hedi, hesp, hebp⟩ =>
      ⟨hh, h.frame.trans hf, hrd.trans h.rd, hwr.trans h.wr, hesi.trans h.esi, hedi.trans h.edi,
        hesp.trans h.esp, hebp.trans h.ebp⟩

theorem doubleRound_ok {B : Addr} {v : CState} {s₀ s : State} (hctx : VG.Proof.ChaCha20.X86.Ctx B s₀)
    (h : VG.Proof.ChaCha20.X86.RI B v s₀ s) : WP isa doubleRound s (VG.Proof.ChaCha20.X86.RI B (innerBlock v) s₀) := by
  unfold doubleRound
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.quarter_step (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) hctx h) fun _ h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.quarter_step (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) hctx h1) fun _ h2 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.quarter_step (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) hctx h2) fun _ h3 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.quarter_step (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) hctx h3) fun _ h4 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.quarter_step (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) hctx h4) fun _ h5 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.quarter_step (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) hctx h5) fun _ h6 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.quarter_step (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) hctx h6) fun _ h7 => ?_)
  exact VG.Proof.ChaCha20.X86.quarter_step (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide) (by decide)
    (by decide) (by decide) hctx h7

theorem rounds_ok {B : Addr} {v : CState} {s₀ : State} (hctx : VG.Proof.ChaCha20.X86.Ctx B s₀) (h : VG.Proof.ChaCha20.X86.Holds B v s₀.mem) :
    ∀ n, WP isa (rounds n) s₀ (VG.Proof.ChaCha20.X86.RI B (Nat.repeat innerBlock n v) s₀)
  | 0 => WP.block_nil ⟨h, Frame.refl _ _, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (VG.Proof.ChaCha20.X86.rounds_ok hctx h n) fun _ h' => VG.Proof.ChaCha20.X86.doubleRound_ok hctx h')

end VG.Proof.ChaCha20.X86

end

/-!
# ChaCha20 block function on x86 (32-bit): the whole function
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20

open VG.X86 in
/-- X86 (32-bit) contract for `vg_chacha20_block(state: *const [u32; 16], buf:
*mut [u32; 64])`, whose arguments are on the stack (cdecl): writes `block` of
the state at `state` to the first 16 words of `buf`.

The same function and Rust signature on every target: the code may
read the two arguments (8 bytes above the return address) and `state` (64
bytes), and read and write `buf` (256 bytes; its first 64 bytes hold the
result on exit, and the rest is scratch space whose contents on exit are
unspecified). `buf` may not overlap `state`, the arguments or the return
address, and nothing may wrap around the end of the (32-bit) address space.
`esp` and the arguments (the pointers) are public; the state (key, counter
and nonce) is secret. -/
def blockX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let buf : Region := ⟨(arg s 1).setWidth 64, 256⟩
    let args : Region := ⟨argAddr s 0, 8⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [state, args] ∧ s.wr = [buf] ∧
    buf.Disjoint state ∧ args.Disjoint buf ∧ ret.Disjoint buf ∧
    (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 256 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 12 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem ((arg s 1).setWidth 64) = block (stateAt s.mem ((arg s 0).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86

open VG VG.X86 VG.Impl.ChaCha20.X86 VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word stateAt innerBlock)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev esp₀ : BitVec 32 := s₀.gpr .esp
/-- The two pointers. -/
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
/-- Their 64-bit addresses. -/
abbrev SA : Addr := (VG.Proof.ChaCha20.X86.st s₀).setWidth 64
abbrev BA : Addr := (VG.Proof.ChaCha20.X86.bp s₀).setWidth 64
abbrev stR : Region := ⟨VG.Proof.ChaCha20.X86.SA s₀, 64⟩
abbrev bufR : Region := ⟨VG.Proof.ChaCha20.X86.BA s₀, 256⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 8⟩
abbrev retR : Region := ⟨(VG.Proof.ChaCha20.X86.esp₀ s₀).setWidth 64, 4⟩
/-- The input state. -/
abbrev V : CState := stateAt s₀.mem (VG.Proof.ChaCha20.X86.SA s₀)
/-- The result of the rounds. -/
abbrev Rs : CState := Nat.repeat innerBlock 10 (VG.Proof.ChaCha20.X86.V s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.ChaCha20.X86.stR s₀, VG.Proof.ChaCha20.X86.argR s₀]
  wr : s₀.wr = [VG.Proof.ChaCha20.X86.bufR s₀]
  buf_st : (VG.Proof.ChaCha20.X86.bufR s₀).Disjoint (VG.Proof.ChaCha20.X86.stR s₀)
  arg_buf : (VG.Proof.ChaCha20.X86.argR s₀).Disjoint (VG.Proof.ChaCha20.X86.bufR s₀)
  ret_buf : (VG.Proof.ChaCha20.X86.retR s₀).Disjoint (VG.Proof.ChaCha20.X86.bufR s₀)
  st_fits : (VG.Proof.ChaCha20.X86.st s₀).toNat + 64 ≤ 2 ^ 32
  buf_fits : (VG.Proof.ChaCha20.X86.bp s₀).toNat + 256 ≤ 2 ^ 32
  esp_fits : (VG.Proof.ChaCha20.X86.esp₀ s₀).toNat + 12 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.ChaCha20.blockX86.pre s₀) : VG.Proof.ChaCha20.X86.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem contains_off {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

/-- A sub-range `[a, a + len)` of `buf` contains `[d, d + n)`. -/
theorem contains_sub (p : Addr) {a len d n : Nat} (h1 : a ≤ d) (h2 : d + n ≤ a + len)
    (h3 : a + len < 2 ^ 32) :
    (⟨p + BitVec.ofNat 64 a, len⟩ : Region).Contains (p + BitVec.ofNat 64 d) n := Offset.contains p h1 h2 (by lit_omega)

namespace Pre
variable {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Pre s₀)
include hp

theorem eaB {d : Nat} (hd : d < 256) : addr (VG.Proof.ChaCha20.X86.bp s₀) d = VG.Proof.ChaCha20.X86.BA s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.buf_fits; omega)

theorem eaS {d : Nat} (hd : d < 64) : addr (VG.Proof.ChaCha20.X86.st s₀) d = VG.Proof.ChaCha20.X86.SA s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fits; omega)

theorem eaA {d : Nat} (hd : d < 12) :
    addr (VG.Proof.ChaCha20.X86.esp₀ s₀) d = (VG.Proof.ChaCha20.X86.esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.esp_fits; omega)

theorem hw : VG.Proof.ChaCha20.X86.bufR s₀ ∈ s₀.wr := by simp [hp.wr]

theorem in_buf {d n : Nat} (h : d + n ≤ 256) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (VG.Proof.ChaCha20.X86.BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨VG.Proof.ChaCha20.X86.bufR s₀, by simp [hp.wr], VG.Proof.ChaCha20.X86.contains_off (by lit_omega) (by lit_omega)⟩

theorem out_buf {d n : Nat} (h : d + n ≤ 256) : InRegions s₀.wr (VG.Proof.ChaCha20.X86.BA s₀ + BitVec.ofNat 64 d) n :=
  ⟨VG.Proof.ChaCha20.X86.bufR s₀, by simp [hp.wr], VG.Proof.ChaCha20.X86.contains_off (by lit_omega) (by lit_omega)⟩

theorem in_st {k : Nat} (hk : k < 16) (ws : List Region) :
    InRegions (s₀.rd ++ ws) (VG.Proof.ChaCha20.X86.SA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨VG.Proof.ChaCha20.X86.stR s₀, by simp [hp.rd], VG.Proof.ChaCha20.X86.contains_off (by lit_omega) (by lit_omega)⟩

/-- An argument slot is inside the argument region. -/
theorem arg_sub {i : Nat} (hi : i < 2) : Region.Sub ⟨argAddr s₀ i, 4⟩ (VG.Proof.ChaCha20.X86.argR s₀) := by
  simp only [VG.Proof.ChaCha20.X86.argR, argAddr]
  rw [show (VG.Proof.ChaCha20.X86.esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (VG.Proof.ChaCha20.X86.esp₀ s₀) 4 from rfl,
    hp.eaA (by lit_omega),
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (VG.Proof.ChaCha20.X86.esp₀ s₀) (4 + 4 * i)
    from rfl, hp.eaA (by lit_omega)]
  exact Offset.sub _ (by lit_omega) (by lit_omega)

theorem arg_contains {i : Nat} (hi : i < 2) : (VG.Proof.ChaCha20.X86.argR s₀).Contains (argAddr s₀ i) 4 := by
  simp only [VG.Proof.ChaCha20.X86.argR]
  rw [show argAddr s₀ i = addr (VG.Proof.ChaCha20.X86.esp₀ s₀) (4 + 4 * i) from rfl, hp.eaA (by lit_omega),
    show argAddr s₀ 0 = addr (VG.Proof.ChaCha20.X86.esp₀ s₀) 4 from rfl, hp.eaA (by lit_omega)]
  exact VG.Proof.ChaCha20.X86.contains_sub _ (by lit_omega) (by lit_omega) (by lit_omega)

theorem in_arg {i : Nat} (hi : i < 2) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨VG.Proof.ChaCha20.X86.argR s₀, by simp [hp.rd], hp.arg_contains hi⟩

/-- Reading the input state after writes to `buf` only. -/
theorem read_st {m : Mem} (hf : Frame [VG.Proof.ChaCha20.X86.bufR s₀] s₀.mem m) {k : Nat} (hk : k < 16) :
    m.readW (VG.Proof.ChaCha20.X86.SA s₀ + BitVec.ofNat 64 (4 * k)) 32 = (VG.Proof.ChaCha20.X86.V s₀)[k] := by
  rw [hf.readW (r := VG.Proof.ChaCha20.X86.stR s₀) (VG.Proof.ChaCha20.X86.contains_off (by lit_omega) (by lit_omega)) (by simpa using hp.buf_st.symm)
    (by decide)]
  simp only [VG.Proof.ChaCha20.X86.V, stateAt, Vector.getElem_ofFn]

end Pre

theorem workR_sub (B : Addr) : Region.Sub (VG.Proof.ChaCha20.X86.workR B) ⟨B, 256⟩ := Region.sub_prefix (by lit_omega)

theorem frame_buf {s₀ : State} {m m' : Mem} (hf : Frame [VG.Proof.ChaCha20.X86.workR (VG.Proof.ChaCha20.X86.BA s₀)] m m') :
    Frame [VG.Proof.ChaCha20.X86.bufR s₀] m m' :=
  hf.sub fun r hr => ⟨VG.Proof.ChaCha20.X86.bufR s₀, List.mem_singleton_self _, by
    simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.ChaCha20.X86.workR_sub _⟩

/-! ## Saving the callee-saved registers, and loading the pointers -/

theorem readW_writeW_off (m : Mem) (p : Addr) (v : Word) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (p + BitVec.ofNat 64 e) v).readW (p + BitVec.ofNat 64 d) 32 =
      m.readW (p + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep p h (by lit_omega) (by lit_omega)) (by decide)

/-- The callee-saved registers `ebx, esi, edi` and their slots in `buf`. -/
def blockSaved : Spill.Slots := [(.ebx, 64), (.esi, 68), (.edi, 72)]

theorem blockSaved_fits : Spill.Fits 76 VG.Proof.ChaCha20.X86.blockSaved := by decide

theorem blockSaved_addr {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Pre s₀) : ∀ p ∈ VG.Proof.ChaCha20.X86.blockSaved, addr (VG.Proof.ChaCha20.X86.bp s₀) p.2 = VG.Proof.ChaCha20.X86.BA s₀ + BitVec.ofNat 64 p.2 :=
  fun p h => hp.eaB (by have := blockSaved_fits.1 p h; lit_omega)

/-- The memory after the prologue's stores. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (VG.Proof.ChaCha20.X86.BA s₀ + BitVec.ofNat 64 ·) s₀.gpr VG.Proof.ChaCha20.X86.blockSaved

/-- The callee-saved registers `ebx, esi, edi` are saved in `buf`. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (VG.Proof.ChaCha20.X86.BA s₀ + BitVec.ofNat 64 ·) s₀.gpr VG.Proof.ChaCha20.X86.blockSaved

theorem saveMem_saved (s₀ : State) : VG.Proof.ChaCha20.X86.Saved s₀ (VG.Proof.ChaCha20.X86.saveMem s₀) :=
  Spill.saveMem_saved_ofNat _ _ _ VG.Proof.ChaCha20.X86.blockSaved_fits (by decide)

theorem saveMem_frame (s₀ : State) : Frame [VG.Proof.ChaCha20.X86.bufR s₀] s₀.mem (VG.Proof.ChaCha20.X86.saveMem s₀) :=
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
    have := blockSaved_fits.1 p h; VG.Proof.ChaCha20.X86.contains_off (by lit_omega) (by lit_omega)

/-- The saved registers survive writes to the working state. -/
theorem saved_frame {s₀ : State} {m m' : Mem} (h : VG.Proof.ChaCha20.X86.Saved s₀ m) (hf : Frame [VG.Proof.ChaCha20.X86.workR (VG.Proof.ChaCha20.X86.BA s₀)] m m') :
    VG.Proof.ChaCha20.X86.Saved s₀ m' :=
  h.of_frame hf (R := ⟨VG.Proof.ChaCha20.X86.BA s₀ + BitVec.ofNat 64 64, 12⟩)
    (fun p hp => by
      have := blockSaved_fits.1 p hp
      have : 64 ≤ p.2 := by revert p hp; decide
      exact Offset.contains _ this (by lit_omega) (by lit_omega))
    (by simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint_base _ (by decide) (by lit_omega))

theorem save_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Pre s₀) :
    WP isa (.block VG.Impl.ChaCha20.X86.save) s₀ fun s₁ =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s₁.gpr r = s₀.gpr r) ∧
      s₁.gpr .esi = VG.Proof.ChaCha20.X86.bp s₀ ∧ s₁.gpr .edi = VG.Proof.ChaCha20.X86.st s₀ ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr ∧
      s₁.mem = VG.Proof.ChaCha20.X86.saveMem s₀ := by
  rw [show VG.Impl.ChaCha20.X86.save = .mov .eax (.mem (at_ .esp 8)) :: .mov .ecx (.mem (at_ .esp 4)) :: (Spill.saveCode .eax VG.Proof.ChaCha20.X86.blockSaved ++
    ([.mov .esi (.reg .eax), .mov .edi (.reg .ecx)] : List Instr)) from rfl]
  refine Wp.wp_ldm rfl (hp.in_arg (i := 1) (by lit_omega)) fun s₁ u₁ => ?_
  refine Wp.wp_ldm (by rw [u₁.other _ (by decide)]) (by rw [u₁.rd, u₁.wr]; exact hp.in_arg (i := 0) (by lit_omega))
    fun s₂ u₂ => ?_
  have hB : s₂.gpr .eax = VG.Proof.ChaCha20.X86.bp s₀ := by rw [u₂.other _ (by decide), u₁.gpr]; rfl
  refine Spill.save_ok VG.Proof.ChaCha20.X86.blockSaved (fun p h => by
      rw [hB, u₂.wr, u₁.wr, VG.Proof.ChaCha20.X86.blockSaved_addr hp p h]; exact hp.out_buf (by have := blockSaved_fits.1 p h; lit_omega))
    fun s₃ u₃ => Wp.wp_mov fun s₄ u₄ => Wp.wp_mov fun s₅ u₅ => WP.block_nil ⟨fun r h1 h2 h3 h4 => ?_, ?_, ?_,
      by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr], ?_⟩
  · rw [u₅.other _ h4, u₄.other _ h3, u₃.gpr, u₂.other _ h2, u₁.other _ h1]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, hB]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.mem]; rfl
  · rw [u₅.mem, u₄.mem, u₃.mem, hB, u₂.mem, u₁.mem]
    exact Spill.saveMem_congr _ _ (VG.Proof.ChaCha20.X86.blockSaved_addr hp) fun p h => by
      have : p.1 ≠ .ecx ∧ p.1 ≠ .eax := by revert p h; decide
      rw [u₂.other _ this.1, u₁.other _ this.2]

/-! ## Copying the state -/

/-- The copy invariant after `n` words, relative to the state `s₁` after the prologue. -/
structure CI (s₀ s₁ : State) (n : Nat) (s : State) : Prop where
  keep : ∀ r, r ≠ .eax → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  fb : Frame [VG.Proof.ChaCha20.X86.bufR s₀] s₀.mem s.mem
  fw : Frame [VG.Proof.ChaCha20.X86.workR (VG.Proof.ChaCha20.X86.BA s₀)] s₁.mem s.mem
  copied : ∀ j (hj : j < 16), j < n → s.mem.readW (VG.Proof.ChaCha20.X86.wordAddr (VG.Proof.ChaCha20.X86.BA s₀) j) 32 = (VG.Proof.ChaCha20.X86.V s₀)[j]

theorem copy_step {s₀ s₁ : State} (hp : VG.Proof.ChaCha20.X86.Pre s₀) (hesi : s₁.gpr .esi = VG.Proof.ChaCha20.X86.bp s₀)
    (hedi : s₁.gpr .edi = VG.Proof.ChaCha20.X86.st s₀) {n : Nat} (hn : n < 16) {s : State} (hc : VG.Proof.ChaCha20.X86.CI s₀ s₁ n s) :
    WP isa (.block (copyWord n)) s (VG.Proof.ChaCha20.X86.CI s₀ s₁ (n + 1)) := by
  have hsi : s.gpr .esi = VG.Proof.ChaCha20.X86.bp s₀ := (hc.keep _ (by decide)).trans hesi
  have hdi : s.gpr .edi = VG.Proof.ChaCha20.X86.st s₀ := (hc.keep _ (by decide)).trans hedi
  have eS : (VG.Proof.ChaCha20.X86.st s₀ + BitVec.ofNat 32 (4 * n)).setWidth 64 = VG.Proof.ChaCha20.X86.SA s₀ + BitVec.ofNat 64 (4 * n) :=
    hp.eaS (by lit_omega)
  have eB : (VG.Proof.ChaCha20.X86.bp s₀ + BitVec.ofNat 32 (4 * n)).setWidth 64 = VG.Proof.ChaCha20.X86.wordAddr (VG.Proof.ChaCha20.X86.BA s₀) n := hp.eaB (by lit_omega)
  have iS : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.X86.SA s₀ + BitVec.ofNat 64 (4 * n)) 4 := by
    rw [hc.rd, hc.wr]; exact hp.in_st hn _
  have oB : InRegions s.wr (VG.Proof.ChaCha20.X86.wordAddr (VG.Proof.ChaCha20.X86.BA s₀) n) 4 := by rw [hc.wr]; exact hp.out_buf (by lit_omega)
  have hv := hp.read_st hc.fb hn
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, copyWord, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.setReg,
    State.ea, at_, State.load32, State.store32, hsi, hdi, eS, eB, iS, oB, hv,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => by simp [hr, hc.keep r hr], hc.rd, hc.wr,
    hc.fb.writeW (List.mem_singleton_self _) _ (VG.Proof.ChaCha20.X86.contains_off (by lit_omega) (by lit_omega)),
    hc.fw.writeW (List.mem_singleton_self _) _ (VG.Proof.ChaCha20.X86.word_in_work _ hn), fun j hj hjn => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
  · rw [VG.Proof.ChaCha20.X86.readW_writeW_word _ _ _ hj hn (by lit_omega)]; exact hc.copied j hj hjn
  · exact Mem.readW_writeW_self32 _ _ _

/-! ## Adding the input state -/

/-- The add invariant after `n` words, relative to the state `sB` after the rounds. -/
structure AI (s₀ sB : State) (n : Nat) (s : State) : Prop where
  out : ∀ j (hj : j < 16), s.mem.readW (VG.Proof.ChaCha20.X86.wordAddr (VG.Proof.ChaCha20.X86.BA s₀) j) 32 =
    if j < n then (VG.Proof.ChaCha20.X86.Rs s₀)[j] + (VG.Proof.ChaCha20.X86.V s₀)[j] else (VG.Proof.ChaCha20.X86.Rs s₀)[j]
  keep : ∀ r, r ≠ .eax → s.gpr r = sB.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  fb : Frame [VG.Proof.ChaCha20.X86.bufR s₀] s₀.mem s.mem
  fw : Frame [VG.Proof.ChaCha20.X86.workR (VG.Proof.ChaCha20.X86.BA s₀)] sB.mem s.mem

theorem add_step {s₀ sB : State} (hp : VG.Proof.ChaCha20.X86.Pre s₀) (hesi : sB.gpr .esi = VG.Proof.ChaCha20.X86.bp s₀)
    (hedi : sB.gpr .edi = VG.Proof.ChaCha20.X86.st s₀) {n : Nat} (hn : n < 16) {s : State} (ha : VG.Proof.ChaCha20.X86.AI s₀ sB n s) :
    WP isa (.block (addWord n)) s (VG.Proof.ChaCha20.X86.AI s₀ sB (n + 1)) := by
  have hsi : s.gpr .esi = VG.Proof.ChaCha20.X86.bp s₀ := (ha.keep _ (by decide)).trans hesi
  have hdi : s.gpr .edi = VG.Proof.ChaCha20.X86.st s₀ := (ha.keep _ (by decide)).trans hedi
  have eS : (VG.Proof.ChaCha20.X86.st s₀ + BitVec.ofNat 32 (4 * n)).setWidth 64 = VG.Proof.ChaCha20.X86.SA s₀ + BitVec.ofNat 64 (4 * n) :=
    hp.eaS (by lit_omega)
  have eB : (VG.Proof.ChaCha20.X86.bp s₀ + BitVec.ofNat 32 (4 * n)).setWidth 64 = VG.Proof.ChaCha20.X86.wordAddr (VG.Proof.ChaCha20.X86.BA s₀) n := hp.eaB (by lit_omega)
  have iS : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.X86.SA s₀ + BitVec.ofNat 64 (4 * n)) 4 := by
    rw [ha.rd, ha.wr]; exact hp.in_st hn _
  have iB : InRegions (s.rd ++ s.wr) (VG.Proof.ChaCha20.X86.wordAddr (VG.Proof.ChaCha20.X86.BA s₀) n) 4 := by
    rw [ha.wr]; exact hp.in_buf (by lit_omega) _
  have oB : InRegions s.wr (VG.Proof.ChaCha20.X86.wordAddr (VG.Proof.ChaCha20.X86.BA s₀) n) 4 := by rw [ha.wr]; exact hp.out_buf (by lit_omega)
  have hv := hp.read_st ha.fb hn
  have hr := ha.out n hn
  simp only [Nat.lt_irrefl, ite_false] at hr
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, Nat.reducePow, addWord, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.setReg, arithFlags, State.setFlags, State.ea, at_, State.load32, State.store32, hsi, hdi,
    eS, eB, iS, iB, oB, hv, hr, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj => ?_, fun r hr => by simp [hr, ha.keep r hr], ha.rd, ha.wr,
    ha.fb.writeW (List.mem_singleton_self _) _ (VG.Proof.ChaCha20.X86.contains_off (by lit_omega) (by lit_omega)),
    ha.fw.writeW (List.mem_singleton_self _) _ (VG.Proof.ChaCha20.X86.word_in_work _ hn)⟩
  by_cases hjn : j = n
  · subst hjn; simp [Mem.readW_writeW_self32]
  · rw [VG.Proof.ChaCha20.X86.readW_writeW_word _ _ _ hj hn hjn, ha.out j hj]
    split <;> split <;> first | omega | rfl

/-! ## Restoring the callee-saved registers -/

theorem restore_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Pre s₀) {s : State} (hs : VG.Proof.ChaCha20.X86.Saved s₀ s.mem)
    (hesi : s.gpr .esi = VG.Proof.ChaCha20.X86.bp s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block VG.Impl.ChaCha20.X86.restore) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr .ebx = s₀.gpr .ebx ∧ s'.gpr .esi = s₀.gpr .esi ∧
      s'.gpr .edi = s₀.gpr .edi ∧ ∀ r, r ≠ .eax → r ≠ .ebx → r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r := by
  rw [show VG.Impl.ChaCha20.X86.restore = .mov .eax (.reg .esi) :: (Spill.restoreCode .eax VG.Proof.ChaCha20.X86.blockSaved ++ []) from rfl]
  refine Wp.wp_mov fun s₁ u₁ => ?_
  have hB : s₁.gpr .eax = VG.Proof.ChaCha20.X86.bp s₀ := by rw [u₁.gpr, hesi]
  refine Spill.restore_ok VG.Proof.ChaCha20.X86.blockSaved (by decide)
    (fun p h => by
      rw [hB, u₁.rd, u₁.wr, hwr, VG.Proof.ChaCha20.X86.blockSaved_addr hp p h]; exact hp.in_buf (by have := blockSaved_fits.1 p h; lit_omega) _)
    (by rw [hB, u₁.mem]; exact hs.congr (fun p h => (VG.Proof.ChaCha20.X86.blockSaved_addr hp p h).symm) fun _ _ => rfl)
    fun s' r' => WP.block_nil ⟨by rw [r'.mem, u₁.mem], r'.gpr (.ebx, 64) (by decide),
      r'.gpr (.esi, 68) (by decide), r'.gpr (.edi, 72) (by decide), fun r h1 h2 h3 h4 => ?_⟩
  rw [r'.other r (by simp [VG.Proof.ChaCha20.X86.blockSaved, h2, h3, h4]), u₁.other _ h1]

/-! ## The whole function -/

theorem finish_split : finish ++ VG.Impl.ChaCha20.X86.restore = (List.range 16).flatMap addWord ++ VG.Impl.ChaCha20.X86.restore := rfl

theorem block_post {p : Addr} {m : Mem} {R v : CState}
    (h : ∀ j (hj : j < 16), m.readW (VG.Proof.ChaCha20.X86.wordAddr p j) 32 = R[j] + v[j]) :
    stateAt m p = Vector.zipWith (· + ·) R v := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_zipWith]
  exact h j hj

theorem correct {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Pre s₀) :
    WP isa block s₀ fun s' => abiPreserved s₀ s' ∧ Proof.ChaCha20.blockX86.post s₀ s' := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.ChaCha20.X86.save_ok hp) fun s₁ ⟨hk₁, hesi₁, hedi₁, hrd₁, hwr₁, hm₁⟩ => ?_
  have hc₀ : VG.Proof.ChaCha20.X86.CI s₀ s₁ 0 s₁ :=
    ⟨fun _ _ => rfl, hrd₁, hwr₁, hm₁ ▸ VG.Proof.ChaCha20.X86.saveMem_frame s₀, Frame.refl _ _,
      fun _ _ h => absurd h (by lit_omega)⟩
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.ChaCha20.X86.CI s₀ s₁)
    (fun k s hk hc => VG.Proof.ChaCha20.X86.copy_step hp hesi₁ hedi₁ hk hc) 16 (Nat.le_refl _) s₁ hc₀) fun s₂ hc => ?_
  have hsi₂ : s₂.gpr .esi = VG.Proof.ChaCha20.X86.bp s₀ := (hc.keep _ (by decide)).trans hesi₁
  have hdi₂ : s₂.gpr .edi = VG.Proof.ChaCha20.X86.st s₀ := (hc.keep _ (by decide)).trans hedi₁
  have hctx : VG.Proof.ChaCha20.X86.Ctx (VG.Proof.ChaCha20.X86.BA s₀) s₂ :=
    ⟨fun k hk => by rw [hsi₂]; exact hp.eaB (by lit_omega),
      fun k hk => by rw [hc.wr]; exact hp.in_buf (by lit_omega) _,
      fun k hk => by rw [hc.wr]; exact hp.out_buf (by lit_omega)⟩
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.rounds_ok hctx (fun k hk => hc.copied k hk hk) 10) fun s₃ hR => ?_)
  rw [VG.Proof.ChaCha20.X86.finish_split, WP.block_append_iff]
  have ha₀ : VG.Proof.ChaCha20.X86.AI s₀ s₃ 0 s₃ :=
    ⟨fun j hj => by simp only [Nat.not_lt_zero, ite_false]; exact hR.holds j hj, fun _ _ => rfl,
      hR.rd.trans hc.rd, hR.wr.trans hc.wr, hc.fb.trans (VG.Proof.ChaCha20.X86.frame_buf hR.frame), Frame.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.ChaCha20.X86.AI s₀ s₃)
    (fun k s hk ha => VG.Proof.ChaCha20.X86.add_step hp (hR.esi.trans hsi₂) (hR.edi.trans hdi₂) hk ha) 16 (Nat.le_refl _) s₃ ha₀)
    fun s₄ hA => ?_
  have hwork : Frame [VG.Proof.ChaCha20.X86.workR (VG.Proof.ChaCha20.X86.BA s₀)] s₁.mem s₄.mem := (hc.fw.trans hR.frame).trans hA.fw
  have hsaved : VG.Proof.ChaCha20.X86.Saved s₀ s₄.mem := VG.Proof.ChaCha20.X86.saved_frame (hm₁ ▸ VG.Proof.ChaCha20.X86.saveMem_saved s₀) hwork
  have hsi₄ : s₄.gpr .esi = VG.Proof.ChaCha20.X86.bp s₀ := (hA.keep _ (by decide)).trans (hR.esi.trans hsi₂)
  refine WP.mono (VG.Proof.ChaCha20.X86.restore_ok hp hsaved hsi₄ hA.wr) fun s' ⟨hm', hbx, hsi, hdi, hk'⟩ => ?_
  have hesp : s'.gpr .esp = s₀.gpr .esp := by
    rw [hk' _ (by decide) (by decide) (by decide) (by decide), hA.keep _ (by decide), hR.esp,
      hc.keep _ (by decide), hk₁ _ (by decide) (by decide) (by decide) (by decide)]
  have hebp : s'.gpr .ebp = s₀.gpr .ebp := by
    rw [hk' _ (by decide) (by decide) (by decide) (by decide), hA.keep _ (by decide), hR.ebp,
      hc.keep _ (by decide), hk₁ _ (by decide) (by decide) (by decide) (by decide)]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hbx
    · exact hsi
    · exact hdi
    · exact hebp
    · exact hesp
  · rw [hm']
    refine hA.fb.readW (r := VG.Proof.ChaCha20.X86.retR s₀) (Region.contains_self _ _) ?_ (by decide)
    simpa using hp.ret_buf
  · show stateAt s'.mem (VG.Proof.ChaCha20.X86.BA s₀) = Spec.ChaCha20.block (VG.Proof.ChaCha20.X86.V s₀)
    rw [hm']
    exact VG.Proof.ChaCha20.X86.block_post fun j hj => by simpa [hj] using hA.out j hj

/-- Memory whose two argument slots (at `0x4004`) hold `0x1000` and `0x2000`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.ChaCha20.X86.satMem
  rd := [⟨0x1000, 64⟩, ⟨0x4004, 8⟩]
  wr := [⟨0x2000, 256⟩]

/-! ## Constant time -/

/-- The initial taint: `esp` is public, and so are the 12 bytes above it (the
return address and the two pointer arguments), which no store changes. -/
def τ₀ : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 12 }

theorem wf₀ {s : State} (hp : VG.Proof.ChaCha20.X86.Pre s) : VG.X86.Taint.Wf VG.Proof.ChaCha20.X86.τ₀ s := by
  have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim, fun _ => ⟨hs, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩
  simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r rfl
  exact VG.X86.Taint.frame_disjoint (n := 8) (by lit_omega) (by simpa using hp.ret_buf)
    (by simpa [VG.Proof.ChaCha20.X86.argR, argAddr, addr] using hp.arg_buf)

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.ChaCha20.blockX86.pre s₁)
    (h₂ : Proof.ChaCha20.blockX86.pre s₂) (hpub : Proof.ChaCha20.blockX86.pub s₁ s₂) :
    VG.X86.Taint.Agree VG.Proof.ChaCha20.X86.τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1⟩ := hpub
  have hp₁ := VG.Proof.ChaCha20.X86.pre_of _ h₁; have hp₂ := VG.Proof.ChaCha20.X86.pre_of _ h₂
  have f₁ : (s₁.gpr .esp).toNat + 12 ≤ 2 ^ 32 := hp₁.esp_fits
  have f₂ : (s₂.gpr .esp).toNat + 12 ≤ 2 ^ 32 := hp₂.esp_fits
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, VG.Proof.ChaCha20.X86.wf₀ hp₁, VG.Proof.ChaCha20.X86.wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.ChaCha20.X86.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · simp only [VG.Proof.ChaCha20.X86.τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by lit_omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by lit_omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1

theorem block_correct (s : State) (hs : Proof.ChaCha20.blockX86.pre s) :
    ∃ t s', Exec isa block s t s' ∧ abiPreserved s s' ∧ Proof.ChaCha20.blockX86.post s s' :=
  VG.Proof.ChaCha20.X86.correct (VG.Proof.ChaCha20.X86.pre_of s hs)

theorem block_ct : ConstantTime isa Proof.ChaCha20.blockX86.pre Proof.ChaCha20.blockX86.pub block :=
  VG.Taint.constantTime (A := taint) VG.Proof.ChaCha20.X86.τ₀ (fun _ _ h₁ h₂ hpub => VG.Proof.ChaCha20.X86.agree₀ h₁ h₂ hpub) (by taint_decide)

theorem block_verified :
    Verified X86.target Impl.ChaCha20.X86.block (Spec.ChaCha20.blockContract X86.abi) :=
  Verified.of_correct VG.Proof.ChaCha20.X86.block_correct VG.Proof.ChaCha20.X86.block_ct (by
    have a0 : arg VG.Proof.ChaCha20.X86.satState 0 = 0x1000 := by decide
    have a1 : arg VG.Proof.ChaCha20.X86.satState 1 = 0x2000 := by decide
    have e : argAddr VG.Proof.ChaCha20.X86.satState 0 = 0x4004 := by decide
    have esp : satState.gpr .esp = 0x4000 := rfl
    sig_implies [Spec.ChaCha20.blockContract, Spec.ChaCha20.blockSig, X86.abi, X86.argSlots,
      X86.argVal, X86.argBytes, Proof.ChaCha20.blockX86] [a0, a1, e, esp] using VG.Proof.ChaCha20.X86.satState)

end VG.Proof.ChaCha20.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86.Bytes`. -/
section

/-!
# ChaCha20 on x86 (32-bit): XORing keystream into data

`xorBytes` XORs the `ecx` bytes at `edx` into those at `esi`, one at a time,
advancing both (`xorLoop` reads the keystream a word at a time and uses its
low byte); `xorWide` does the same 16 bytes at a time first.
-/

namespace VG.Proof.ChaCha20.X86.Bytes

open VG VG.X86
open VG.Impl.ChaCha20.X86 (at_ xb)
open VG.Impl.ChaCha20.X86.Xor (xorBody xorLoop xorBytes chunkBody xorWide)

theorem toNat_ofNat_lt32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem writeW8_apply (m : Mem) (a x : Addr) (v : Byte) :
    (m.writeW a v) x = if x = a then v else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have h0 : (x - a).toNat = 0 := by omega
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by rw [h0]; rfl)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add a
    simp only [this, h, ↓reduceIte]

/-- The low byte of a word in memory is its first byte. -/
theorem low_byte (m : Mem) (a : Addr) : (m.readW a 32).setWidth 8 = m a := by
  have := Mem.readW_byte m a (i := 0) (by lit_omega)
  rw [show a + BitVec.ofNat 64 0 = a by simp] at this
  rw [this]
  ext i hi
  simp

theorem xor_low (b : Byte) (w : BitVec 32) : (b.setWidth 32 ^^^ w).setWidth 8 = b ^^^ w.setWidth 8 := by
  ext i hi; simp

/-- `p + k`, as the code computes it, without wrapping around. -/
theorem ptr_add (x : BitVec 32) {k : Nat} (h : x.toNat + k < 2 ^ 32) :
    (x + BitVec.ofNat 32 k + BitVec.ofNat 32 0).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem add_ofNat_one (x : BitVec 32) (n : Nat) :
    x + BitVec.ofNat 32 n + 1 = x + BitVec.ofNat 32 (n + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- What `xorBytes` needs: `c` bytes at `D` to write and at `K` to read (a
word at a time), not overlapping. -/
structure BPre (s : VG.X86.State) (D K : BitVec 32) (c : Nat) : Prop where
  esi : s.gpr .esi = D
  edx : s.gpr .edx = K
  ecx : s.gpr .ecx = BitVec.ofNat 32 c
  d_fit : D.toNat + c ≤ 2 ^ 32
  k_fit : K.toNat + c < 2 ^ 32
  wD : ∀ k < c, InRegions s.wr (D.setWidth 64 + BitVec.ofNat 64 k) 1
  rK : ∀ k < c, InRegions (s.rd ++ s.wr) (K.setWidth 64 + BitVec.ofNat 64 k) 4
  sep : ∀ j < c, ∀ k < c, D.setWidth 64 + BitVec.ofNat 64 j ≠ K.setWidth 64 + BitVec.ofNat 64 k

/-- What `xorBytes` leaves: the bytes XORed, and `esi`, `edx` past them;
only `eax`, `ecx`, `edx` and `esi` are written. -/
structure BPost (s : VG.X86.State) (D K : BitVec 32) (c : Nat) (s' : VG.X86.State) : Prop where
  esi : s'.gpr .esi = D + BitVec.ofNat 32 c
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D.setWidth 64 + BitVec.ofNat 64 k) =
    s.mem (D.setWidth 64 + BitVec.ofNat 64 k) ^^^ s.mem (K.setWidth 64 + BitVec.ofNat 64 k)
  frame : Frame [⟨D.setWidth 64, c⟩] s.mem s'.mem

/-- Before byte `i`. -/
structure LInv (s : VG.X86.State) (D K : BitVec 32) (c i : Nat) (s' : VG.X86.State) : Prop where
  esi : s'.gpr .esi = D + BitVec.ofNat 32 i
  edx : s'.gpr .edx = K + BitVec.ofNat 32 i
  ecx : s'.gpr .ecx = BitVec.ofNat 32 (c - i)
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D.setWidth 64 + BitVec.ofNat 64 k) =
    if k < i then s.mem (D.setWidth 64 + BitVec.ofNat 64 k) ^^^ s.mem (K.setWidth 64 + BitVec.ofNat 64 k)
    else s.mem (D.setWidth 64 + BitVec.ofNat 64 k)
  frame : Frame [⟨D.setWidth 64, c⟩] s.mem s'.mem

theorem D_ne {D : Addr} {c j k : Nat} (hc : c ≤ 2 ^ 32) (hj : j < c) (hk : k < c) (h : j ≠ k) :
    D + BitVec.ofNat 64 j ≠ D + BitVec.ofNat 64 k := by
  intro he
  have e : BitVec.ofNat 64 j = BitVec.ofNat 64 k := by
    have e := congrArg (· - D) he; simpa using e
  have := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  exact h this

/-- A byte read is outside the bytes written. -/
theorem not_contains {D K : Addr} {c i : Nat}
    (hs : ∀ j < c, ∀ k < c, D + BitVec.ofNat 64 j ≠ K + BitVec.ofNat 64 k) (hi : i < c)
    (h : (⟨D, c⟩ : Region).Contains (K + BitVec.ofNat 64 i) 1) : False := by
  simp only [Region.Contains] at h
  refine hs (K + BitVec.ofNat 64 i - D).toNat (by omega) i hi ?_
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]

theorem ofNat32_beq_zero {x : Nat} (hx : x < 2 ^ 32) : (BitVec.ofNat 32 x == 0) = decide (x = 0) := by
  by_cases h : x = 0
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [VG.Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 hx] at this
    exact h this

set_option simprocs false in
theorem byte_step {s : VG.X86.State} {D K : BitVec 32} {c i : Nat} (hp : VG.Proof.ChaCha20.X86.Bytes.BPre s D K c) (hi : i < c) {s₁ : VG.X86.State}
    (h : VG.Proof.ChaCha20.X86.Bytes.LInv s D K c i s₁) :
    WP isa (.block xorBody) s₁ fun s' => VG.Proof.ChaCha20.X86.Bytes.LInv s D K c (i + 1) s' ∧ s'.zf = some (decide (c - (i + 1) = 0)) := by
  have hc := hp.d_fit
  have hk := hp.k_fit
  have ea₁ : (D + BitVec.ofNat 32 i + BitVec.ofNat 32 0).setWidth 64 = D.setWidth 64 + BitVec.ofNat 64 i :=
    VG.Proof.ChaCha20.X86.Bytes.ptr_add _ (by omega)
  have ea₂ : (K + BitVec.ofNat 32 i + BitVec.ofNat 32 0).setWidth 64 = K.setWidth 64 + BitVec.ofNat 64 i :=
    VG.Proof.ChaCha20.X86.Bytes.ptr_add _ (by omega)
  have cd : (⟨D.setWidth 64, c⟩ : Region).Contains (D.setWidth 64 + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  have i₁ : InRegions (s₁.rd ++ s₁.wr) (D.setWidth 64 + BitVec.ofNat 64 i) 1 := by
    obtain ⟨r, hr, hc⟩ := hp.wD i hi; exact ⟨r, by rw [h.rd, h.wr]; exact List.mem_append_right _ hr, hc⟩
  have i₂ : InRegions (s₁.rd ++ s₁.wr) (K.setWidth 64 + BitVec.ofNat 64 i) 4 := by
    rw [h.rd, h.wr]; exact hp.rK i hi
  have o₁ : InRegions s₁.wr (D.setWidth 64 + BitVec.ofNat 64 i) 1 := by rw [h.wr]; exact hp.wD i hi
  apply WP.of_runBlock
  simp (config := {decide := true}) only [xorBody, at_, runBlock_cons, runStep_some,
    runBlock_nil, exec, State.ea, VG.X86.readSrc, execAlu, arithFlags, State.load8, State.load32,
    State.store8, State.setReg, State.setFlags, Reg8.reg, h.esi, h.edx, ea₁, ea₂, i₁, i₂, o₁,
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hk' : s₁.mem (K.setWidth 64 + BitVec.ofNat 64 i) = s.mem (K.setWidth 64 + BitVec.ofNat 64 i) :=
    h.frame _ fun r hr hcont => by
      simp only [List.mem_singleton] at hr; subst hr
      exact VG.Proof.ChaCha20.X86.Bytes.not_contains hp.sep hi hcont
  have hd : s₁.mem (D.setWidth 64 + BitVec.ofNat 64 i) = s.mem (D.setWidth 64 + BitVec.ofNat 64 i) := by
    rw [h.data i hi]; simp
  rw [VG.Proof.ChaCha20.X86.Bytes.xor_low, VG.Proof.ChaCha20.X86.Bytes.low_byte, hd, hk']
  have hfd : Frame [⟨D.setWidth 64, c⟩] s₁.mem (s₁.mem.writeW (D.setWidth 64 + BitVec.ofNat 64 i)
      (s.mem (D.setWidth 64 + BitVec.ofNat 64 i) ^^^ s.mem (K.setWidth 64 + BitVec.ofNat 64 i))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ cd
  have hsub : BitVec.ofNat 32 (c - i) - 1 = BitVec.ofNat 32 (c - (i + 1)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, VG.Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by omega)]; simp; omega),
      VG.Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by omega), VG.Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by omega)]
    simp; omega
  refine ⟨⟨?_, ?_, ?_, fun r h₁ h₂ h₃ h₄ => ?_, h.rd, h.wr, fun k hk' => ?_, h.frame.trans hfd⟩, ?_⟩
  · simp (config := {decide := true}) only [ite_true, ite_false]
    exact VG.Proof.ChaCha20.X86.Bytes.add_ofNat_one _ _
  · simp (config := {decide := true}) only [ite_true, ite_false]
    exact VG.Proof.ChaCha20.X86.Bytes.add_ofNat_one _ _
  · simp (config := {decide := true}) only [ite_true, ite_false, h.ecx]
    exact hsub
  · simp only [h₁, h₂, h₃, h₄, ite_false]; exact h.keep r h₁ h₂ h₃ h₄
  · dsimp only; rw [VG.Proof.ChaCha20.X86.Bytes.writeW8_apply]
    by_cases he : k = i
    · subst he; simp
    · have hne := VG.Proof.ChaCha20.X86.Bytes.D_ne (D := D.setWidth 64) (by omega) hk' hi he
      simp only [hne, ite_false]
      rw [h.data k hk']
      by_cases h₁ : k < i
      · simp [h₁, show k < i + 1 by omega]
      · simp [h₁, show ¬ k < i + 1 by omega]
  · simp only [h.ecx, hsub, VG.Proof.ChaCha20.X86.Bytes.ofNat32_beq_zero (show c - (i + 1) < 2 ^ 32 by omega)]

theorem LInv.zero {s : VG.X86.State} {D K : BitVec 32} {c : Nat} (hp : VG.Proof.ChaCha20.X86.Bytes.BPre s D K c) : VG.Proof.ChaCha20.X86.Bytes.LInv s D K c 0 s :=
  ⟨by rw [hp.esi]; simp, by rw [hp.edx]; simp, by rw [hp.ecx, Nat.sub_zero], fun _ _ _ _ _ => rfl, rfl, rfl,
    fun k _ => by simp, Frame.refl _ _⟩

theorem LInv.post {s : VG.X86.State} {D K : BitVec 32} {c : Nat} {s' : VG.X86.State} (h : VG.Proof.ChaCha20.X86.Bytes.LInv s D K c c s') :
    VG.Proof.ChaCha20.X86.Bytes.BPost s D K c s' :=
  ⟨h.esi, h.keep, h.rd, h.wr, fun k hk => by rw [h.data k hk, ite_eq_left hk], h.frame⟩

theorem loop_ok {s : VG.X86.State} {D K : BitVec 32} {c : Nat} (hp : VG.Proof.ChaCha20.X86.Bytes.BPre s D K c) (hc0 : c ≠ 0) :
    WP isa xorLoop s (VG.Proof.ChaCha20.X86.Bytes.BPost s D K c) := by
  have hc := hp.d_fit
  let Inv : Nat → VG.X86.State → Prop := fun n s' => ∃ i, n = c - i ∧ i < c ∧ VG.Proof.ChaCha20.X86.Bytes.LInv s D K c i s'
  have hstep : ∀ n s', Inv n s' → WP isa (.block xorBody) s' (fun s'' =>
      (isa.eval .ne s'' = some false ∧ VG.Proof.ChaCha20.X86.Bytes.BPost s D K c s'') ∨
      (isa.eval .ne s'' = some true ∧ ∃ n' < n, Inv n' s'')) := by
    rintro n s' ⟨i, rfl, hi, hI⟩
    refine WP.mono (VG.Proof.ChaCha20.X86.Bytes.byte_step hp hi hI) fun s'' ⟨h', hz⟩ => ?_
    have he : isa.eval .ne s'' = some (!decide (c - (i + 1) = 0)) := by
      show eval .ne s'' = _
      simp only [eval, hz, Option.map_some]
    by_cases hl : i + 1 = c
    · exact .inl ⟨by rw [he]; simp; omega, LInv.post (hl ▸ h')⟩
    · exact .inr ⟨by rw [he]; simp; omega, c - (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep c s ⟨0, by simp, by omega, LInv.zero hp⟩

set_option simprocs false in
theorem test_ecx_ok {s : VG.X86.State} {c : Nat} (h : s.gpr .ecx = BitVec.ofNat 32 c) (hc : c < 2 ^ 32) :
    WP isa (.block [.alu .test .ecx (.reg .ecx)]) s fun s' => s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = some (decide (c = 0)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86.readSrc, execAlu, arithFlags, State.setFlags,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, ?_⟩
  rw [BitVec.and_self, h, VG.Proof.ChaCha20.X86.Bytes.ofNat32_beq_zero hc]

theorem xorBytes_eq : xorBytes = .seq (.block [.alu .test .ecx (.reg .ecx)]) (.ite .e (.block []) xorLoop) := rfl

theorem xorBytes_ok {s : VG.X86.State} {D K : BitVec 32} {c : Nat} (hp : VG.Proof.ChaCha20.X86.Bytes.BPre s D K c) :
    WP isa xorBytes s (VG.Proof.ChaCha20.X86.Bytes.BPost s D K c) := by
  have hc := hp.d_fit
  rw [VG.Proof.ChaCha20.X86.Bytes.xorBytes_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Bytes.test_ecx_ok hp.ecx (by have := hp.k_fit; omega)) fun s₁ ⟨g₁, m₁, r₁, w₁, z₁⟩ => ?_)
  have hp₁ : VG.Proof.ChaCha20.X86.Bytes.BPre s₁ D K c := ⟨by rw [g₁, hp.esi], by rw [g₁, hp.edx], by rw [g₁, hp.ecx], hp.d_fit, hp.k_fit,
    fun k hk => by rw [w₁]; exact hp.wD k hk, fun k hk => by rw [r₁, w₁]; exact hp.rK k hk,
    hp.sep⟩
  have conv : ∀ s', VG.Proof.ChaCha20.X86.Bytes.BPost s₁ D K c s' → VG.Proof.ChaCha20.X86.Bytes.BPost s D K c s' := fun s' h =>
    ⟨h.esi, fun r a b d e => by rw [h.keep r a b d e, g₁], by rw [h.rd, r₁], by rw [h.wr, w₁],
      fun k hk => by rw [h.data k hk, m₁], m₁ ▸ h.frame⟩
  refine WP.ite (decide (c = 0)) (by show eval .e s₁ = _; simp only [eval, z₁])
    (fun h0 => WP.block_nil (M := isa) (conv _ ?_)) (fun h0 => WP.mono (VG.Proof.ChaCha20.X86.Bytes.loop_ok hp₁ (by simpa using h0)) conv)
  simp only [decide_eq_true_eq] at h0; subst h0; exact (LInv.zero hp₁).post


/-! ## 16 bytes at a time -/

/-- A byte at offset `k` after a 16-byte write at offset `off`. -/
theorem byte_write16 (m : Mem) (a : Addr) (v : BitVec 128) {off k : Nat} (ho : off + 16 ≤ 2 ^ 32)
    (hk : k < 2 ^ 32) : (m.writeW (a + BitVec.ofNat 64 off) v) (a + BitVec.ofNat 64 k) =
      if off ≤ k ∧ k < off + 16 then v.extractLsb' (8 * (k - off)) 8 else m (a + BitVec.ofNat 64 k) := by
  by_cases h : off ≤ k ∧ k < off + 16
  · rw [ite_eq_left h, show a + BitVec.ofNat 64 k = a + BitVec.ofNat 64 off + BitVec.ofNat 64 (k - off) by
      rw [Offset.add_add, Nat.add_sub_cancel' h.1]]
    exact writeW_byte _ _ _ (by omega) (by lit_omega)
  · rw [ite_eq_right h]
    refine writeW_byte_off _ _ _ _ ?_
    rw [Offset.sub_toNat' a (by lit_omega) (by lit_omega)]
    split <;> omega

/-- What `xorWide` needs: `c` bytes at `D` to write, and `c + 3` at `K` to
read (the bytes a word at a time), not overlapping. -/
structure WPre (s : VG.X86.State) (D K : BitVec 32) (c : Nat) : Prop where
  esi : s.gpr .esi = D
  edx : s.gpr .edx = K
  ecx : s.gpr .ecx = BitVec.ofNat 32 c
  d_fit : D.toNat + c ≤ 2 ^ 32
  k_fit : K.toNat + c + 3 < 2 ^ 32
  wD : ∀ off n, off + n ≤ c → InRegions s.wr (D.setWidth 64 + BitVec.ofNat 64 off) n
  rK : ∀ off n, off + n ≤ c + 3 → InRegions (s.rd ++ s.wr) (K.setWidth 64 + BitVec.ofNat 64 off) n
  sep : (⟨D.setWidth 64, c⟩ : Region).Disjoint ⟨K.setWidth 64, c + 3⟩

/-- After `i` chunks of 16 bytes. -/
structure CInv (s : VG.X86.State) (D K : BitVec 32) (c i : Nat) (s' : VG.X86.State) : Prop where
  esi : s'.gpr .esi = D + BitVec.ofNat 32 (16 * i)
  edx : s'.gpr .edx = K + BitVec.ofNat 32 (16 * i)
  ecx : s'.gpr .ecx = BitVec.ofNat 32 (c - 16 * i)
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  data : ∀ k < c, s'.mem (D.setWidth 64 + BitVec.ofNat 64 k) =
    if k < 16 * i then s.mem (D.setWidth 64 + BitVec.ofNat 64 k) ^^^ s.mem (K.setWidth 64 + BitVec.ofNat 64 k)
    else s.mem (D.setWidth 64 + BitVec.ofNat 64 k)
  frame : Frame [⟨D.setWidth 64, c⟩] s.mem s'.mem

theorem WPre.kbyte {s : VG.X86.State} {D K : BitVec 32} {c : Nat} (hp : VG.Proof.ChaCha20.X86.Bytes.WPre s D K c) {m : Mem}
    (hf : Frame [⟨D.setWidth 64, c⟩] s.mem m) {k : Nat} (hk : k < c + 3) :
    m (K.setWidth 64 + BitVec.ofNat 64 k) = s.mem (K.setWidth 64 + BitVec.ofNat 64 k) :=
  hf _ fun r hr hc => by
    have := hp.k_fit
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.sep _ hc (Offset.contains_base _ (by omega) (by lit_omega))

theorem sub_ofNat32 {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 32) :
    BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem add_ofNat32 (x : BitVec 32) (a b : Nat) :
    x + BitVec.ofNat 32 a + BitVec.ofNat 32 b = x + BitVec.ofNat 32 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem ea_setXmm (s : VG.X86.State) (r : XReg) (v : BitVec 128) (m : MemOp) : (s.setXmm r v).ea m = s.ea m := rfl

theorem chunk_step {s : VG.X86.State} {D K : BitVec 32} {c i : Nat} (hp : VG.Proof.ChaCha20.X86.Bytes.WPre s D K c) (hi : 16 * (i + 1) ≤ c)
    {s₁ : VG.X86.State} (h : VG.Proof.ChaCha20.X86.Bytes.CInv s D K c i s₁) :
    WP isa (.block chunkBody) s₁ fun s' =>
      VG.Proof.ChaCha20.X86.Bytes.CInv s D K c (i + 1) s' ∧ s'.cf = some (decide (c - 16 * (i + 1) < 16)) := by
  have hc := hp.d_fit
  have hk := hp.k_fit
  have ea₁ : s₁.ea (at_ .esi 0) = D.setWidth 64 + BitVec.ofNat 64 (16 * i) := by
    show (s₁.gpr .esi + BitVec.ofNat 32 0).setWidth 64 = _
    rw [h.esi]; exact VG.Proof.ChaCha20.X86.Bytes.ptr_add _ (by omega)
  have ea₂ : s₁.ea (at_ .edx 0) = K.setWidth 64 + BitVec.ofNat 64 (16 * i) := by
    show (s₁.gpr .edx + BitVec.ofNat 32 0).setWidth 64 = _
    rw [h.edx]; exact VG.Proof.ChaCha20.X86.Bytes.ptr_add _ (by omega)
  have o₁ : InRegions s₁.wr (D.setWidth 64 + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [h.wr]; exact hp.wD _ _ (by omega)
  have i₁ : InRegions (s₁.rd ++ s₁.wr) (D.setWidth 64 + BitVec.ofNat 64 (16 * i)) 16 :=
    let ⟨r, hr, hc⟩ := o₁; ⟨r, List.mem_append_right _ hr, hc⟩
  have i₂ : InRegions (s₁.rd ++ s₁.wr) (K.setWidth 64 + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [h.rd, h.wr]; exact hp.rK _ _ (by omega)
  rw [show chunkBody = [.movdquLoad .xmm4 (at_ .esi 0), .movdquLoad .xmm5 (at_ .edx 0), xb .pxor .xmm4 .xmm5,
      .movdquStore (at_ .esi 0) .xmm4] ++ [.alu .add .esi (.imm 16), .alu .add .edx (.imm 16),
      .alu .sub .ecx (.imm 16), .alu .cmp .ecx (.imm 16)] from rfl, WP.block_append_iff]
  refine WP.mono (Q := fun s₂ : VG.X86.State => s₂.gpr = s₁.gpr ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr ∧
      s₂.mem = s₁.mem.writeW (D.setWidth 64 + BitVec.ofNat 64 (16 * i))
        (s₁.mem.readW (D.setWidth 64 + BitVec.ofNat 64 (16 * i)) 128 ^^^
          s₁.mem.readW (K.setWidth 64 + BitVec.ofNat 64 (16 * i)) 128)) ?_ fun s₂ ⟨g₂, r₂, w₂, m₂⟩ => ?_
  · apply WP.of_runBlock
    simp only [xb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128,
      State.store128, VG.Proof.ChaCha20.X86.Bytes.ea_setXmm, ea₁, ea₂, i₁, i₂, RegUpd.wr_setXmm, o₁, ite_true,
      RegUpd.mem_setXmm, RegUpd.gpr_setXmm, RegUpd.rd_setXmm, Option.map_some, Option.some.injEq,
      exists_eq_left']
    refine ⟨trivial, trivial, trivial, ?_⟩
    simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ (by decide : ¬ XReg.xmm4 = .xmm5),
      XBinOp.eval]
  refine Wp.wp_addi fun s₃ u₃ => ?_
  refine Wp.wp_addi fun s₄ u₄ => ?_
  refine Wp.wp_subi fun s₅ u₅ _ _ => ?_
  refine Wp.wp_cmpi fun s₆ u₆ hcf _ => WP.block_nil ⟨⟨?_, ?_, ?_, fun r a b d e => ?_, ?_, ?_,
    fun k hk' => ?_, ?_⟩, ?_⟩
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, h.esi, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, VG.Proof.ChaCha20.X86.Bytes.add_ofNat32]; rfl
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂, h.edx, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, VG.Proof.ChaCha20.X86.Bytes.add_ofNat32]; rfl
  · rw [u₆.gpr, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, h.ecx,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, VG.Proof.ChaCha20.X86.Bytes.sub_ofNat32 (by omega) (by omega)]
    exact congrArg (BitVec.ofNat 32) (by omega)
  · rw [u₆.gpr, u₅.other _ b, u₄.other _ d, u₃.other _ e, g₂, h.keep r a b d e]
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, r₂, h.rd]
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, w₂, h.wr]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂, VG.Proof.ChaCha20.X86.Bytes.byte_write16 _ _ _ (by omega) (by omega)]
    by_cases hin : 16 * i ≤ k ∧ k < 16 * i + 16
    · rw [ite_eq_left hin, ite_eq_left (by omega), BitVec.extractLsb'_xor, byte_readW _ _ (by omega),
        byte_readW _ _ (by omega), Offset.add_add, Offset.add_add, Nat.add_sub_cancel' hin.1, h.data k hk',
        ite_eq_right (by omega), hp.kbyte h.frame (by omega)]
    · rw [ite_eq_right hin, h.data k hk']
      by_cases hlt : k < 16 * i
      · rw [ite_eq_left hlt, ite_eq_left (by omega)]
      · rw [ite_eq_right hlt, ite_eq_right (by omega)]
  · rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, m₂]
    exact h.frame.trans ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by lit_omega)))
  · rw [hcf, u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, h.ecx,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, VG.Proof.ChaCha20.X86.Bytes.sub_ofNat32 (by omega) (by omega),
      VG.Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by omega), VG.Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by omega)]
    exact congrArg (fun n => some (decide (n < 16))) (by omega)

theorem CInv.zero {s : VG.X86.State} {D K : BitVec 32} {c : Nat} (hp : VG.Proof.ChaCha20.X86.Bytes.WPre s D K c) : VG.Proof.ChaCha20.X86.Bytes.CInv s D K c 0 s :=
  ⟨by rw [hp.esi]; simp, by rw [hp.edx]; simp, by rw [hp.ecx]; simp, fun _ _ _ _ _ => rfl, rfl, rfl,
    fun k _ => by simp, Frame.refl _ _⟩

theorem chunks_ok {s : VG.X86.State} {D K : BitVec 32} {c : Nat} (hp : VG.Proof.ChaCha20.X86.Bytes.WPre s D K c) (hc : 16 ≤ c) :
    WP isa (.loop (.block chunkBody) .ae) s (VG.Proof.ChaCha20.X86.Bytes.CInv s D K c (c / 16)) := by
  let Inv : Nat → VG.X86.State → Prop := fun n s' => ∃ i, n = c - 16 * i ∧ 16 * (i + 1) ≤ c ∧ VG.Proof.ChaCha20.X86.Bytes.CInv s D K c i s'
  have hstep : ∀ n s', Inv n s' → WP isa (.block chunkBody) s' (fun s'' =>
      (isa.eval .ae s'' = some false ∧ VG.Proof.ChaCha20.X86.Bytes.CInv s D K c (c / 16) s'') ∨
      (isa.eval .ae s'' = some true ∧ ∃ n' < n, Inv n' s'')) := by
    rintro n s' ⟨i, rfl, hi, hI⟩
    refine WP.mono (VG.Proof.ChaCha20.X86.Bytes.chunk_step hp hi hI) fun s'' ⟨h', hcf⟩ => ?_
    have he : isa.eval .ae s'' = some (!decide (c - 16 * (i + 1) < 16)) := by
      show eval .ae s'' = _
      simp only [eval, hcf, Option.map_some]
    by_cases hl : c - 16 * (i + 1) < 16
    · exact .inl ⟨by rw [he]; simp [hl], by rwa [show c / 16 = i + 1 by omega]⟩
    · exact .inr ⟨by rw [he]; simp [hl], c - 16 * (i + 1), by omega, i + 1, rfl, by omega, h'⟩
  exact WP.loop (M := isa) Inv hstep c s ⟨0, by simp, by omega, CInv.zero hp⟩

theorem xorWide_eq : xorWide = .seq (.block [.alu .cmp .ecx (.imm 16)])
    (.seq (.ite .b (.block []) (.loop (.block chunkBody) .ae)) xorBytes) := rfl

/-- The flags of `cmp` and nothing else. -/
theorem cmpi_ok (s : VG.X86.State) (d : Reg) (v : BitVec 32) :
    WP isa (.block [.alu .cmp d (.imm v)]) s fun s' => s'.gpr = s.gpr ∧ s'.mem = s.mem ∧
      s'.xmm = s.xmm ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.cf = some (decide ((s.gpr d).toNat < v.toNat)) :=
  Wp.cons rfl (WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem ofNat32_add_toNat (x : BitVec 32) {n : Nat} (h : x.toNat + n < 2 ^ 32) :
    (x + BitVec.ofNat 32 n).toNat = x.toNat + n := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem setWidth_add (x : BitVec 32) {n : Nat} (h : x.toNat + n < 2 ^ 32) :
    (x + BitVec.ofNat 32 n).setWidth 64 = x.setWidth 64 + BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem xorWide_ok {s : VG.X86.State} {D K : BitVec 32} {c : Nat} (hp : VG.Proof.ChaCha20.X86.Bytes.WPre s D K c) :
    WP isa xorWide s (VG.Proof.ChaCha20.X86.Bytes.BPost s D K c) := by
  have hc := hp.d_fit
  have hk := hp.k_fit
  rw [VG.Proof.ChaCha20.X86.Bytes.xorWide_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Bytes.cmpi_ok s .ecx 16) fun s₁ ⟨g₁, m₁, _, r₁, w₁, c₁⟩ => ?_)
  rw [hp.ecx, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, VG.Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by omega),
    VG.Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by omega)] at c₁
  have hp₁ : VG.Proof.ChaCha20.X86.Bytes.WPre s₁ D K c := ⟨by rw [g₁, hp.esi], by rw [g₁, hp.edx], by rw [g₁, hp.ecx], hc, hk,
    fun o n h => by rw [w₁]; exact hp.wD o n h, fun o n h => by rw [r₁, w₁]; exact hp.rK o n h, hp.sep⟩
  have conv : ∀ s', VG.Proof.ChaCha20.X86.Bytes.BPost s₁ D K c s' → VG.Proof.ChaCha20.X86.Bytes.BPost s D K c s' := fun s' h =>
    ⟨h.esi, fun r a b d e => by rw [h.keep r a b d e, g₁], by rw [h.rd, r₁], by rw [h.wr, w₁],
      fun k hk => by rw [h.data k hk, m₁], m₁ ▸ h.frame⟩
  refine WP.mono (Q := VG.Proof.ChaCha20.X86.Bytes.BPost s₁ D K c) ?_ conv
  refine WP.seq (WP.mono (Q := VG.Proof.ChaCha20.X86.Bytes.CInv s₁ D K c (c / 16)) ?_ fun s₂ h₂ => ?_)
  · refine WP.ite (decide (c < 16)) (by show eval .b s₁ = _; simp only [eval, c₁]) (fun h => ?_)
      (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      rw [show c / 16 = 0 by omega]; exact WP.block_nil (CInv.zero hp₁)
    · simp only [decide_eq_false_iff_not, Nat.not_lt] at h
      exact VG.Proof.ChaCha20.X86.Bytes.chunks_ok hp₁ h
  -- The bytes after the last multiple of 16.
  have hq : 16 * (c / 16) ≤ c := Nat.mul_div_le c 16
  have hK : K.toNat + 16 * (c / 16) < 2 ^ 32 := by omega
  have eK : (K + BitVec.ofNat 32 (16 * (c / 16))).setWidth 64 = K.setWidth 64 + BitVec.ofNat 64 (16 * (c / 16)) :=
    VG.Proof.ChaCha20.X86.Bytes.setWidth_add _ hK
  have eD : ∀ t, t < c - 16 * (c / 16) →
      (D + BitVec.ofNat 32 (16 * (c / 16))).setWidth 64 + BitVec.ofNat 64 t = D.setWidth 64 + BitVec.ofNat 64 (16 * (c / 16) + t) := by
    intro t ht
    rw [VG.Proof.ChaCha20.X86.Bytes.setWidth_add _ (by omega), Offset.add_add]
  have eK' : ∀ t, (K + BitVec.ofNat 32 (16 * (c / 16))).setWidth 64 + BitVec.ofNat 64 t =
      K.setWidth 64 + BitVec.ofNat 64 (16 * (c / 16) + t) := fun t => by rw [eK, Offset.add_add]
  have hb : VG.Proof.ChaCha20.X86.Bytes.BPre s₂ (D + BitVec.ofNat 32 (16 * (c / 16))) (K + BitVec.ofNat 32 (16 * (c / 16)))
      (c - 16 * (c / 16)) := by
    refine ⟨h₂.esi, h₂.edx, h₂.ecx, ?_, by rw [VG.Proof.ChaCha20.X86.Bytes.ofNat32_add_toNat _ hK]; omega, fun t ht => ?_, fun t ht => ?_,
      fun t ht t' ht' he => ?_⟩
    · by_cases hz : c - 16 * (c / 16) = 0
      · rw [hz]; exact Nat.le_of_lt (BitVec.isLt _)
      · rw [VG.Proof.ChaCha20.X86.Bytes.ofNat32_add_toNat _ (by omega)]; omega
    · rw [eD t ht, h₂.wr]; exact hp₁.wD _ _ (by omega)
    · rw [eK', h₂.rd, h₂.wr]; exact hp₁.rK _ _ (by omega)
    · rw [eD t ht, eK'] at he
      exact hp.sep (D.setWidth 64 + BitVec.ofNat 64 (16 * (c / 16) + t))
        (Offset.contains_base _ (by omega) (by lit_omega))
        (by rw [he]; exact Offset.contains_base _ (by omega) (by lit_omega))
  refine WP.mono (VG.Proof.ChaCha20.X86.Bytes.xorBytes_ok hb) fun s₃ h₃ => ⟨?_, fun r a b d e => ?_, ?_, ?_, fun k hk' => ?_, ?_⟩
  · rw [h₃.esi, VG.Proof.ChaCha20.X86.Bytes.add_ofNat32, Nat.add_sub_cancel' hq]
  · rw [h₃.keep r a b d e, h₂.keep r a b d e]
  · rw [h₃.rd, h₂.rd]
  · rw [h₃.wr, h₂.wr]
  · by_cases hlt : k < 16 * (c / 16)
    · have hf : s₃.mem (D.setWidth 64 + BitVec.ofNat 64 k) = s₂.mem (D.setWidth 64 + BitVec.ofNat 64 k) := by
        refine h₃.frame _ fun r hr hcon => ?_
        simp only [List.mem_singleton] at hr; subst hr
        simp only [Region.Contains] at hcon
        rw [VG.Proof.ChaCha20.X86.Bytes.setWidth_add _ (by omega), Offset.sub_toNat' _ (by lit_omega) (by lit_omega)] at hcon
        split at hcon <;> omega
      rw [hf, h₂.data k hk', ite_eq_left hlt]
    · obtain ⟨t, rfl⟩ : ∃ t, k = 16 * (c / 16) + t := ⟨k - 16 * (c / 16), by omega⟩
      have h3 := h₃.data t (by omega)
      rw [eD t (by omega), eK'] at h3
      rw [h3, h₂.data _ hk', ite_eq_right hlt, hp₁.kbyte h₂.frame (by omega)]
  · refine h₂.frame.trans (h₃.frame.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    by_cases hz : c - 16 * (c / 16) = 0
    · rw [hz]; intro x hx; simp only [Region.Contains] at hx; omega
    · rw [VG.Proof.ChaCha20.X86.Bytes.setWidth_add _ (by omega)]
      exact Offset.sub_base _ (by omega)


/-- `and` with `0xfffffff0`: rounding down to a multiple of 16. -/
theorem and_m16 (x : BitVec 32) : x &&& (0xfffffff0 : BitVec 32) = BitVec.ofNat 32 (x.toNat / 16 * 16) := by
  have : (0xfffffff0 : BitVec 32) = BitVec.ofNat 32 ((2 ^ 28 - 1) <<< 4) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hx := x.isLt
  generalize x.toNat = n at *
  rw [Nat.mod_eq_of_lt (by decide), Nat.mod_eq_of_lt (by omega),
    show n / 16 * 16 = (n >>> 4) <<< 4 by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : 4 ≤ i
  · by_cases h2 : i - 4 < 28
    · simp [hi, h2, show 4 + (i - 4) = i by omega]
    · have : n.testBit i = false := Nat.testBit_lt_two_pow (by
        calc n < 2 ^ 32 := hx
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
      simp [hi, h2, this, show 4 + (i - 4) = i by omega]
  · simp [hi]

/-- `and` with 15: the remainder modulo 16. -/
theorem and_15 (x : BitVec 32) : x &&& (15 : BitVec 32) = BitVec.ofNat 32 (x.toNat % 16) := by
  have : (15 : BitVec 32) = BitVec.ofNat 32 (2 ^ 4 - 1) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ 4 - 1 < 2 ^ 32 by decide), Nat.and_two_pow_sub_one_eq_mod]
  omega

end VG.Proof.ChaCha20.X86.Bytes

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86.Vqr`. -/
section

/-!
# ChaCha20 on x86 (32-bit): the quarter round on XMM registers

`vqr a b c d` computes the quarter round on each doubleword of `a, b, c, d`.
-/

namespace VG.Proof.ChaCha20.X86

open VG VG.X86 VG.Impl.ChaCha20.X86
open VG.Spec.ChaCha20 (Word quarterRound)

/-! ## The quarter round on XMM registers -/

theorem rot12 (x : Word) : x <<< 12 ||| x >>> 20 = x.rotateLeft 12 := shl_or_shr x (by decide) (by decide)
theorem rot8 (x : Word) : x <<< 8 ||| x >>> 24 = x.rotateLeft 8 := shl_or_shr x (by decide) (by decide)
theorem rot7 (x : Word) : x <<< 7 ||| x >>> 25 = x.rotateLeft 7 := shl_or_shr x (by decide) (by decide)

theorem pslld_12 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld x (BitVec.ofNat 8 12)) i = dword x i <<< 12 := dword_pslld x _ (by decide) hi
theorem psrld_20 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld x (BitVec.ofNat 8 20)) i = dword x i >>> 20 := dword_psrld x _ (by decide) hi
theorem pslld_8 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld x (BitVec.ofNat 8 8)) i = dword x i <<< 8 := dword_pslld x _ (by decide) hi
theorem psrld_24 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld x (BitVec.ofNat 8 24)) i = dword x i >>> 24 := dword_psrld x _ (by decide) hi
theorem pslld_7 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld x (BitVec.ofNat 8 7)) i = dword x i <<< 7 := dword_pslld x _ (by decide) hi
theorem psrld_25 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld x (BitVec.ofNat 8 25)) i = dword x i >>> 25 := dword_psrld x _ (by decide) hi

/-- Doubleword `l` of register `r`. -/
abbrev dw (s : State) (r : XReg) (l : Nat) : Word := dword (s.xmm r) l

theorem ea_setXmm' (s : State) (r : XReg) (v : BitVec 128) (m : MemOp) : (s.setXmm r v).ea m = s.ea m := rfl

/-- The quarter round on each doubleword of `a, b, c, d`, and only them and
`xmm7` written. -/
def QrPost (a b c d : XReg) (s s' : State) : Prop :=
  (∀ l, l < 4 →
    VG.Proof.ChaCha20.X86.dw s' a l = (quarterRound (VG.Proof.ChaCha20.X86.dw s a l) (VG.Proof.ChaCha20.X86.dw s b l) (VG.Proof.ChaCha20.X86.dw s c l) (VG.Proof.ChaCha20.X86.dw s d l)).1 ∧
    VG.Proof.ChaCha20.X86.dw s' b l = (quarterRound (VG.Proof.ChaCha20.X86.dw s a l) (VG.Proof.ChaCha20.X86.dw s b l) (VG.Proof.ChaCha20.X86.dw s c l) (VG.Proof.ChaCha20.X86.dw s d l)).2.1 ∧
    VG.Proof.ChaCha20.X86.dw s' c l = (quarterRound (VG.Proof.ChaCha20.X86.dw s a l) (VG.Proof.ChaCha20.X86.dw s b l) (VG.Proof.ChaCha20.X86.dw s c l) (VG.Proof.ChaCha20.X86.dw s d l)).2.2.1 ∧
    VG.Proof.ChaCha20.X86.dw s' d l = (quarterRound (VG.Proof.ChaCha20.X86.dw s a l) (VG.Proof.ChaCha20.X86.dw s b l) (VG.Proof.ChaCha20.X86.dw s c l) (VG.Proof.ChaCha20.X86.dw s d l)).2.2.2) ∧
  (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → r ≠ .xmm7 → s'.xmm r = s.xmm r) ∧
  s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

/-- `vqr a b c d` computes the quarter round on each doubleword of `a, b, c,
d` (four distinct registers other than `xmm7`), writing only them and `xmm7`. -/
theorem vqr_ok {a b c d : XReg} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (ha : a ≠ .xmm7) (hb : b ≠ .xmm7) (hc : c ≠ .xmm7)
    (hd : d ≠ .xmm7) (s : State) : WP isa (.block (vqr a b c d)) s (VG.Proof.ChaCha20.X86.QrPost a b c d s) := by
  unfold VG.Proof.ChaCha20.X86.QrPost
  apply WP.of_runBlock
  simp only [vqr, vrot, xb, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, XOp.exec, RegUpd.gpr_setXmm, RegUpd.mem_setXmm, RegUpd.rd_setXmm,
    RegUpd.wr_setXmm, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun r h0 h1 h2 h3 h4 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [VG.Proof.ChaCha20.X86.dw, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ hab, RegUpd.xmm_setXmm_of_ne _ _ hac,
      RegUpd.xmm_setXmm_of_ne _ _ had, RegUpd.xmm_setXmm_of_ne _ _ hbc, RegUpd.xmm_setXmm_of_ne _ _ hbd,
      RegUpd.xmm_setXmm_of_ne _ _ hcd, RegUpd.xmm_setXmm_of_ne _ _ hab.symm,
      RegUpd.xmm_setXmm_of_ne _ _ hac.symm, RegUpd.xmm_setXmm_of_ne _ _ had.symm,
      RegUpd.xmm_setXmm_of_ne _ _ hbc.symm, RegUpd.xmm_setXmm_of_ne _ _ hbd.symm,
      RegUpd.xmm_setXmm_of_ne _ _ hcd.symm, RegUpd.xmm_setXmm_of_ne _ _ ha, RegUpd.xmm_setXmm_of_ne _ _ hb,
      RegUpd.xmm_setXmm_of_ne _ _ hc, RegUpd.xmm_setXmm_of_ne _ _ hd, RegUpd.xmm_setXmm_of_ne _ _ ha.symm,
      RegUpd.xmm_setXmm_of_ne _ _ hb.symm, RegUpd.xmm_setXmm_of_ne _ _ hc.symm, RegUpd.xmm_setXmm_of_ne _ _ hd.symm,
      eval_movdqa]
    simp only [dword_paddd _ _ hl, dword_pxor, dword_por, dword_rot16 _ hl, VG.Proof.ChaCha20.X86.pslld_12 _ hl,
      VG.Proof.ChaCha20.X86.psrld_20 _ hl, VG.Proof.ChaCha20.X86.pslld_8 _ hl, VG.Proof.ChaCha20.X86.psrld_24 _ hl, VG.Proof.ChaCha20.X86.pslld_7 _ hl, VG.Proof.ChaCha20.X86.psrld_25 _ hl, VG.Proof.ChaCha20.X86.rot12, VG.Proof.ChaCha20.X86.rot8, VG.Proof.ChaCha20.X86.rot7,
      quarterRound, and_self]
  · simp only [RegUpd.xmm_setXmm_of_ne _ _ h0, RegUpd.xmm_setXmm_of_ne _ _ h1, RegUpd.xmm_setXmm_of_ne _ _ h2,
      RegUpd.xmm_setXmm_of_ne _ _ h3, RegUpd.xmm_setXmm_of_ne _ _ h4]

/-! ## With SSSE3: rotations by `pshufb` -/

/-- The `pshufb` controls of `vqr3`, as 128-bit values. -/
def mask16 : BitVec 128 := 0x0d0c0f0e09080b0a0504070601000302#128
def mask8 : BitVec 128 := 0x0e0d0c0f0a09080b0605040702010003#128

theorem pshufb16_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a VG.Proof.ChaCha20.X86.mask16 = ofBytes fun j => byte a (4 * (j / 4) + (j % 4 + 2) % 4) := by
  simp only [XBinOp.eval, ofBytes, VG.Proof.ChaCha20.X86.mask16]
  rfl

theorem pshufb8_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a VG.Proof.ChaCha20.X86.mask8 = ofBytes fun j => byte a (4 * (j / 4) + (j % 4 + 3) % 4) := by
  simp only [XBinOp.eval, ofBytes, VG.Proof.ChaCha20.X86.mask8]
  rfl

/-- Byte `j` of each doubleword from byte `(j + t) % 4` is a rotation left by `32 - 8 t`. -/
theorem dword_rotBytes (x : BitVec 128) {i t : Nat} (hi : i < 4) (ht : 0 < t ∧ t < 4) :
    dword (ofBytes fun j => byte x (4 * (j / 4) + (j % 4 + t) % 4)) i = (dword x i).rotateLeft (32 - 8 * t) := by
  apply BitVec.eq_of_getLsbD_eq; intro m hm
  rw [getLsbD_dword, decide_eq_true hm, Bool.true_and,
    show 32 * i + m = 8 * (4 * i + m / 8) + m % 8 by omega, getLsbD_ofBytes _ (by omega) (by omega),
    byte, BitVec.getLsbD_extractLsb', decide_eq_true (by omega), Bool.true_and, BitVec.getLsbD_rotateLeft]
  rw [show (32 - 8 * t) % 32 = 32 - 8 * t by omega]
  by_cases h : m < 32 - 8 * t
  · rw [ite_eq_left h, getLsbD_dword, decide_eq_true (by omega), Bool.true_and]
    exact congrArg _ (by omega)
  · rw [ite_eq_right h, decide_eq_true hm, Bool.true_and, getLsbD_dword, decide_eq_true (by omega),
      Bool.true_and]
    exact congrArg _ (by omega)

theorem dword_pshufb16 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .pshufb x VG.Proof.ChaCha20.X86.mask16) i = (dword x i).rotateLeft 16 := by
  rw [VG.Proof.ChaCha20.X86.pshufb16_bytes, VG.Proof.ChaCha20.X86.dword_rotBytes _ hi (t := 2) (by decide)]

theorem dword_pshufb8 (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (XBinOp.eval .pshufb x VG.Proof.ChaCha20.X86.mask8) i = (dword x i).rotateLeft 8 := by
  rw [VG.Proof.ChaCha20.X86.pshufb8_bytes, VG.Proof.ChaCha20.X86.dword_rotBytes _ hi (t := 3) (by decide)]

/-- `vqr3 a b c d` computes the quarter round on each doubleword of `a, b, c,
d` (four distinct registers other than `xmm7`), writing only them and `xmm7`,
with `edi` pointing at memory holding its controls. -/
theorem vqr3_ok {a b c d : XReg} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (ha : a ≠ .xmm7) (hb : b ≠ .xmm7) (hc : c ≠ .xmm7)
    (hd : d ≠ .xmm7) {p₁ p₂ : Addr} (s : State) (e₁ : s.ea (at_ .edi rot16Off) = p₁)
    (e₂ : s.ea (at_ .edi rot8Off) = p₂) (i₁ : InRegions (s.rd ++ s.wr) p₁ 16)
    (i₂ : InRegions (s.rd ++ s.wr) p₂ 16) (m₁ : s.mem.readW p₁ 128 = VG.Proof.ChaCha20.X86.mask16)
    (m₂ : s.mem.readW p₂ 128 = VG.Proof.ChaCha20.X86.mask8) : WP isa (.block (vqr3 a b c d)) s (VG.Proof.ChaCha20.X86.QrPost a b c d s) := by
  unfold VG.Proof.ChaCha20.X86.QrPost
  apply WP.of_runBlock
  simp only [vqr3, vrot, xb, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
    runBlock_nil, exec, XOp.exec, State.load128, VG.Proof.ChaCha20.X86.ea_setXmm', e₁, e₂, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    RegUpd.mem_setXmm, i₁, i₂, ite_true, Option.map_some, m₁, m₂, RegUpd.gpr_setXmm,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun r h0 h1 h2 h3 h4 => ?_, trivial, trivial, trivial, trivial⟩
  · simp only [VG.Proof.ChaCha20.X86.dw, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ hab, RegUpd.xmm_setXmm_of_ne _ _ hac,
      RegUpd.xmm_setXmm_of_ne _ _ had, RegUpd.xmm_setXmm_of_ne _ _ hbc, RegUpd.xmm_setXmm_of_ne _ _ hbd,
      RegUpd.xmm_setXmm_of_ne _ _ hcd, RegUpd.xmm_setXmm_of_ne _ _ hab.symm,
      RegUpd.xmm_setXmm_of_ne _ _ hac.symm, RegUpd.xmm_setXmm_of_ne _ _ had.symm,
      RegUpd.xmm_setXmm_of_ne _ _ hbc.symm, RegUpd.xmm_setXmm_of_ne _ _ hbd.symm,
      RegUpd.xmm_setXmm_of_ne _ _ hcd.symm, RegUpd.xmm_setXmm_of_ne _ _ ha, RegUpd.xmm_setXmm_of_ne _ _ hb,
      RegUpd.xmm_setXmm_of_ne _ _ hc, RegUpd.xmm_setXmm_of_ne _ _ hd,
      RegUpd.xmm_setXmm_of_ne _ _ hb.symm, RegUpd.xmm_setXmm_of_ne _ _ hc.symm, RegUpd.xmm_setXmm_of_ne _ _ hd.symm,
      eval_movdqa]
    simp only [dword_paddd _ _ hl, dword_pxor, dword_por, VG.Proof.ChaCha20.X86.dword_pshufb16 _ hl, VG.Proof.ChaCha20.X86.dword_pshufb8 _ hl,
      VG.Proof.ChaCha20.X86.pslld_12 _ hl, VG.Proof.ChaCha20.X86.psrld_20 _ hl, VG.Proof.ChaCha20.X86.pslld_7 _ hl, VG.Proof.ChaCha20.X86.psrld_25 _ hl, VG.Proof.ChaCha20.X86.rot12, VG.Proof.ChaCha20.X86.rot7, quarterRound, and_self]
  · simp only [RegUpd.xmm_setXmm_of_ne _ _ h0, RegUpd.xmm_setXmm_of_ne _ _ h1, RegUpd.xmm_setXmm_of_ne _ _ h2,
      RegUpd.xmm_setXmm_of_ne _ _ h3, RegUpd.xmm_setXmm_of_ne _ _ h4]

end VG.Proof.ChaCha20.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86.Quad`. -/
section

/-!
# ChaCha20 on x86 (32-bit): four blocks at once with SSE2

Doubleword `l` of each slot of `buf` (and of each register) holds a word of
block `l`; each quarter round of the code is the specification's on each of
the four blocks. During the rounds a word is in its slot or in a register
(`Loc`); one lemma (`step_ok`) covers every quarter round of `plan`, whose
loads, registers and stores are checked against where the words are by
evaluation (`stepOk`). The output XORs each 16 bytes of keystream into the
data if they lie within it, and stores the 16 bytes that run past its end in
`buf[0, 16)` (`chunk_ok`).
-/

namespace VG.Proof.ChaCha20.X86.Quad

open VG VG.X86 VG.Impl.ChaCha20.X86 VG.Impl.ChaCha20.X86.Xor
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)
open VG.Proof.ChaCha20
open VG.Proof.ChaCha20.X86.Bytes (byte_write16 cmpi_ok)

/-! ## The slots -/

/-- `buf`, as far as the four-block code uses it. -/
abbrev bufR (buf : Addr) : Region := ⟨buf, 320⟩

/-- The slots of the sixteen words, `buf[0, 256)`. -/
abbrev slotsR (buf : Addr) : Region := ⟨buf, 256⟩

/-- The four states `vs 0, …, vs 3` are in the slots: word `k` of state `l`
in doubleword `l` of slot `k`. -/
def Holds4 (buf : Addr) (vs : Nat → CState) (m : Mem) : Prop :=
  ∀ k (hk : k < 16) l, l < 4 → m.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 = (vs l)[k]

theorem ea_setXmm (s : State) (r : XReg) (v : BitVec 128) (m : MemOp) : (s.setXmm r v).ea m = s.ea m := rfl

theorem ea_withMem (s : State) (m : Mem) (o : MemOp) : ({ s with mem := m } : State).ea o = s.ea o := rfl

theorem ea_gpr {s s' : State} (h : s'.gpr = s.gpr) (m : MemOp) : s'.ea m = s.ea m := by
  simp only [State.ea, h]

theorem in_buf {rs ws : List Region} {buf : Addr} (hw : VG.Proof.ChaCha20.X86.Quad.bufR buf ∈ ws) {d n : Nat} (h : d + n ≤ 320) :
    InRegions (rs ++ ws) (buf + BitVec.ofNat 64 d) n :=
  ⟨VG.Proof.ChaCha20.X86.Quad.bufR buf, List.mem_append_right _ hw, Offset.contains_base buf h (by lit_omega)⟩

theorem out_buf {ws : List Region} {buf : Addr} (hw : VG.Proof.ChaCha20.X86.Quad.bufR buf ∈ ws) {d n : Nat} (h : d + n ≤ 320) :
    InRegions ws (buf + BitVec.ofNat 64 d) n :=
  ⟨VG.Proof.ChaCha20.X86.Quad.bufR buf, hw, Offset.contains_base buf h (by lit_omega)⟩

theorem lane_load (m : Mem) (buf : Addr) (d : Nat) {l : Nat} (hl : l < 4) :
    dword (m.readW (buf + BitVec.ofNat 64 d) 128) l = m.readW (buf + BitVec.ofNat 64 (d + 4 * l)) 32 := by
  rw [dword_readW _ _ hl, Offset.add_add]

theorem lane_write_self (m : Mem) (buf : Addr) (v : BitVec 128) (d : Nat) {l : Nat} (hl : l < 4) :
    (m.writeW (buf + BitVec.ofNat 64 d) v).readW (buf + BitVec.ofNat 64 (d + 4 * l)) 32 = dword v l := by
  rw [← Offset.add_add, readW_writeW128 _ _ _ hl]

theorem lane_write_other (m : Mem) (buf : Addr) (v : BitVec 128) {d e : Nat} (hd : d + 4 ≤ 2 ^ 32)
    (he : e + 16 ≤ 2 ^ 32) (h : d + 4 ≤ e ∨ e + 16 ≤ d) :
    (m.writeW (buf + BitVec.ofNat 64 e) v).readW (buf + BitVec.ofNat 64 d) 32 =
      m.readW (buf + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep buf h (by lit_omega) (by lit_omega)) (by decide)

theorem slots_frame_write {rs : List Region} {m m' : Mem} {buf : Addr} (h : Frame rs m m')
    (hr : VG.Proof.ChaCha20.X86.Quad.slotsR buf ∈ rs) (v : BitVec 128) {k : Nat} (hk : k < 16) :
    Frame rs m (m'.writeW (buf + BitVec.ofNat 64 (slot k)) v) :=
  h.writeW hr _ (Offset.contains_base buf (by simp only [slot]; omega) (by simp only [slot]; lit_omega))

/-! ## One quarter round on the four states -/

theorem lane_qr {m : Mem} {buf : Addr} {vs : Nat → CState} (h : VG.Proof.ChaCha20.X86.Quad.Holds4 buf vs m) {x : Nat}
    (hx : x < 16) {l : Nat} (hl : l < 4) :
    dword (m.readW (buf + BitVec.ofNat 64 (slot x)) 128) l = (vs l)[x] := by
  rw [VG.Proof.ChaCha20.X86.Quad.lane_load _ _ _ hl]; exact h x hx l hl

/-- Reading lane `l` of slot `k` after writing slot `k'`. -/
theorem lane_other (m : Mem) (buf : Addr) (v : BitVec 128) {k k' l : Nat} (hk : k < 16)
    (hk' : k' < 16) (hl : l < 4) (h : k' ≠ k) :
    (m.writeW (buf + BitVec.ofNat 64 (slot k')) v).readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 =
      m.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 :=
  VG.Proof.ChaCha20.X86.Quad.lane_write_other _ _ _ (by lit_omega) (by simp only [slot]; omega) (by simp only [slot]; omega)

theorem lane_self (m : Mem) (buf : Addr) (v : BitVec 128) (k : Nat) {l : Nat} (hl : l < 4) :
    (m.writeW (buf + BitVec.ofNat 64 (slot k)) v).readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 =
      dword v l :=
  VG.Proof.ChaCha20.X86.Quad.lane_write_self _ _ _ _ hl

/-! ## Words in registers

During the rounds, word `k` of the four states is in its slot or, doubleword
`l` for block `l`, in a register (`L k`). -/

/-- Where each word is: in a register, or in its slot (`none`). -/
abbrev Loc := Nat → Option XReg

/-- `L` with word `k` at `v`. -/
def upd (L : VG.Proof.ChaCha20.X86.Quad.Loc) (k : Nat) (v : Option XReg) : VG.Proof.ChaCha20.X86.Quad.Loc := fun j => if j = k then v else L j

/-- Word `k` of block `l`, where `L` says it is. -/
def val (buf : Addr) (L : VG.Proof.ChaCha20.X86.Quad.Loc) (s : State) (k l : Nat) : Word :=
  match L k with
  | some r => dword (s.xmm r) l
  | none => s.mem.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32

/-- The four states `vs` are where `L` says. -/
def HoldsR (buf : Addr) (L : VG.Proof.ChaCha20.X86.Quad.Loc) (vs : Nat → CState) (s : State) : Prop :=
  ∀ k (hk : k < 16) l, l < 4 → VG.Proof.ChaCha20.X86.Quad.val buf L s k l = (vs l)[k]

theorem val_some {buf : Addr} {L : VG.Proof.ChaCha20.X86.Quad.Loc} {s : State} {k : Nat} {r : XReg} (h : L k = some r) (l : Nat) :
    VG.Proof.ChaCha20.X86.Quad.val buf L s k l = dword (s.xmm r) l := by
  simp only [VG.Proof.ChaCha20.X86.Quad.val, h]

theorem val_none {buf : Addr} {L : VG.Proof.ChaCha20.X86.Quad.Loc} {s : State} {k : Nat} (h : L k = none) (l : Nat) :
    VG.Proof.ChaCha20.X86.Quad.val buf L s k l = s.mem.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 := by
  simp only [VG.Proof.ChaCha20.X86.Quad.val, h]

theorem HoldsR.congr {buf : Addr} {L L' : VG.Proof.ChaCha20.X86.Quad.Loc} {vs : Nat → CState} {s : State}
    (he : ∀ j, j < 16 → L j = L' j) (h : VG.Proof.ChaCha20.X86.Quad.HoldsR buf L vs s) : VG.Proof.ChaCha20.X86.Quad.HoldsR buf L' vs s := fun k hk l hl => by
  rw [← h k hk l hl]; simp only [VG.Proof.ChaCha20.X86.Quad.val, he k hk]

/-- The loads of a quarter round: each word into a register not in use. -/
def loadsOk : VG.Proof.ChaCha20.X86.Quad.Loc → List (XReg × Nat) → Bool
  | _, [] => true
  | L, p :: ps => decide (p.2 < 16 ∧ L p.2 = none ∧ ∀ j : Nat, j < 16 → L j ≠ some p.1) &&
      VG.Proof.ChaCha20.X86.Quad.loadsOk (VG.Proof.ChaCha20.X86.Quad.upd L p.2 (some p.1)) ps

def loadsLoc : VG.Proof.ChaCha20.X86.Quad.Loc → List (XReg × Nat) → VG.Proof.ChaCha20.X86.Quad.Loc
  | L, [] => L
  | L, p :: ps => VG.Proof.ChaCha20.X86.Quad.loadsLoc (VG.Proof.ChaCha20.X86.Quad.upd L p.2 (some p.1)) ps

/-- The stores of a quarter round: each word from the register it is in. -/
def storesOk : VG.Proof.ChaCha20.X86.Quad.Loc → List (Nat × XReg) → Bool
  | _, [] => true
  | L, p :: ps => decide (p.1 < 16 ∧ L p.1 = some p.2) && VG.Proof.ChaCha20.X86.Quad.storesOk (VG.Proof.ChaCha20.X86.Quad.upd L p.1 none) ps

def storesLoc : VG.Proof.ChaCha20.X86.Quad.Loc → List (Nat × XReg) → VG.Proof.ChaCha20.X86.Quad.Loc
  | L, [] => L
  | L, p :: ps => VG.Proof.ChaCha20.X86.Quad.storesLoc (VG.Proof.ChaCha20.X86.Quad.upd L p.1 none) ps

/-- The quarter round on `x, y, z, w`: they are in `q`'s registers, distinct
and not `xmm7`, which hold no other word; no word is in `xmm7`. -/
def quadOk (L : VG.Proof.ChaCha20.X86.Quad.Loc) (q : QStep) (x y z w : Nat) : Bool := decide (
  L x = some q.a ∧ L y = some q.b ∧ L z = some q.c ∧ L w = some q.d ∧
  q.a ≠ q.b ∧ q.a ≠ q.c ∧ q.a ≠ q.d ∧ q.b ≠ q.c ∧ q.b ≠ q.d ∧ q.c ≠ q.d ∧
  q.a ≠ .xmm7 ∧ q.b ≠ .xmm7 ∧ q.c ≠ .xmm7 ∧ q.d ≠ .xmm7 ∧
  (∀ j : Nat, j < 16 → L j ≠ some .xmm7) ∧
  ∀ j : Nat, j < 16 → j = x ∨ j = y ∨ j = z ∨ j = w ∨
    (L j ≠ some q.a ∧ L j ≠ some q.b ∧ L j ≠ some q.c ∧ L j ≠ some q.d))

def stepOk (L : VG.Proof.ChaCha20.X86.Quad.Loc) (q : QStep) (x y z w : Nat) : Bool :=
  VG.Proof.ChaCha20.X86.Quad.loadsOk L q.loads && VG.Proof.ChaCha20.X86.Quad.quadOk (VG.Proof.ChaCha20.X86.Quad.loadsLoc L q.loads) q x y z w && VG.Proof.ChaCha20.X86.Quad.storesOk (VG.Proof.ChaCha20.X86.Quad.loadsLoc L q.loads) q.stores

def stepLoc (L : VG.Proof.ChaCha20.X86.Quad.Loc) (q : QStep) : VG.Proof.ChaCha20.X86.Quad.Loc := VG.Proof.ChaCha20.X86.Quad.storesLoc (VG.Proof.ChaCha20.X86.Quad.loadsLoc L q.loads) q.stores

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (buf : Addr) (L : VG.Proof.ChaCha20.X86.Quad.Loc) (vs : Nat → CState) (s₀ s : State) : Prop where
  holds : VG.Proof.ChaCha20.X86.Quad.HoldsR buf L vs s
  frame : Frame [VG.Proof.ChaCha20.X86.Quad.slotsR buf] s₀.mem s.mem
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem RI.congr {buf : Addr} {L L' : VG.Proof.ChaCha20.X86.Quad.Loc} {vs : Nat → CState} {s₀ s : State}
    (he : ∀ j, j < 16 → L j = L' j) (h : VG.Proof.ChaCha20.X86.Quad.RI buf L vs s₀ s) : VG.Proof.ChaCha20.X86.Quad.RI buf L' vs s₀ s :=
  ⟨h.holds.congr he, h.frame, h.gpr, h.rd, h.wr⟩

/-- `buf[288, 320)`, where a quarter round may keep constants. -/
abbrev kR (buf : Addr) : Region := ⟨buf + BitVec.ofNat 64 288, 32⟩

/-- What the four-block code needs of its quarter round `k.qr`: that it
computes the quarter round given what `k.init` leaves in `buf[288, 320)`
(`Inv`), which only writes there undo. -/
structure KernelOk (k : Kernel) where
  Inv : Addr → Mem → Prop
  inv_frame : ∀ {buf : Addr} {m m' : Mem} {rs : List Region}, Inv buf m → Frame rs m m' →
    (∀ r ∈ rs, (VG.Proof.ChaCha20.X86.Quad.kR buf).Disjoint r) → Inv buf m'
  qr_ok : ∀ {buf : Addr} {a b c d : XReg}, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    a ≠ .xmm7 → b ≠ .xmm7 → c ≠ .xmm7 → d ≠ .xmm7 → ∀ s : State,
    (∀ e, e < 320 → s.ea (at_ .edi e) = buf + BitVec.ofNat 64 e) → VG.Proof.ChaCha20.X86.Quad.bufR buf ∈ s.wr → Inv buf s.mem →
    WP isa (.block (k.qr a b c d)) s (VG.Proof.ChaCha20.X86.QrPost a b c d s)
  init_ok : ∀ {buf : Addr} (s : State), (∀ e, e < 320 → s.ea (at_ .edi e) = buf + BitVec.ofNat 64 e) →
    VG.Proof.ChaCha20.X86.Quad.bufR buf ∈ s.wr → WP isa (.block k.init) s fun s' => Inv buf s'.mem ∧ Frame [VG.Proof.ChaCha20.X86.Quad.kR buf] s.mem s'.mem ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem kR_slots (buf : Addr) : (VG.Proof.ChaCha20.X86.Quad.kR buf).Disjoint (VG.Proof.ChaCha20.X86.Quad.slotsR buf) := Offset.disjoint_base _ (by decide) (by decide)

section
variable {buf : Addr} {s₀ : State} (hb : ∀ d, d < 320 → s₀.ea (at_ .edi d) = buf + BitVec.ofNat 64 d)
  (hwb : VG.Proof.ChaCha20.X86.Quad.bufR buf ∈ s₀.wr)
include hb hwb

theorem ld_ok {L : VG.Proof.ChaCha20.X86.Quad.Loc} {vs : Nat → CState} {s : State} {r : XReg} {k : Nat} (hk : k < 16)
    (hn : L k = none) (hr : ∀ j, j < 16 → L j ≠ some r) (h : VG.Proof.ChaCha20.X86.Quad.RI buf L vs s₀ s) :
    WP isa (.block [ld r k]) s (VG.Proof.ChaCha20.X86.Quad.RI buf (VG.Proof.ChaCha20.X86.Quad.upd L k (some r)) vs s₀) := by
  have e := (VG.Proof.ChaCha20.X86.Quad.ea_gpr h.gpr _).trans (hb (slot k) (by simp only [slot]; omega))
  have i := VG.Proof.ChaCha20.X86.Quad.in_buf (rs := s.rd) (h.wr ▸ hwb) (d := slot k) (n := 16) (by simp only [slot]; omega)
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, e, i, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj l hl => ?_, h.frame, h.gpr, h.rd, h.wr⟩
  have hv := h.holds j hj l hl
  by_cases hjk : j = k
  · subst hjk
    rw [VG.Proof.ChaCha20.X86.Quad.val_some (show VG.Proof.ChaCha20.X86.Quad.upd L j (some r) j = some r from ite_eq_left rfl), RegUpd.xmm_setXmm_self,
      VG.Proof.ChaCha20.X86.Quad.lane_load _ _ _ hl, ← hv, VG.Proof.ChaCha20.X86.Quad.val_none hn]
    rfl
  · have hu : VG.Proof.ChaCha20.X86.Quad.upd L k (some r) j = L j := ite_eq_right hjk
    rcases hL : L j with _ | r'
    · rw [VG.Proof.ChaCha20.X86.Quad.val_none (hu.trans hL)]; rw [VG.Proof.ChaCha20.X86.Quad.val_none hL] at hv; exact hv
    · rw [VG.Proof.ChaCha20.X86.Quad.val_some (hu.trans hL), RegUpd.xmm_setXmm_of_ne _ _ fun e => hr j hj (by rw [hL, e])]
      rw [VG.Proof.ChaCha20.X86.Quad.val_some hL] at hv; exact hv

theorem loads_ok {vs : Nat → CState} : ∀ (ps : List (XReg × Nat)) (L : VG.Proof.ChaCha20.X86.Quad.Loc) (s : State),
    VG.Proof.ChaCha20.X86.Quad.loadsOk L ps = true → VG.Proof.ChaCha20.X86.Quad.RI buf L vs s₀ s →
    WP isa (.block (ps.map fun p => ld p.1 p.2)) s (VG.Proof.ChaCha20.X86.Quad.RI buf (VG.Proof.ChaCha20.X86.Quad.loadsLoc L ps) vs s₀)
  | [], _, _, _, h => WP.block_nil h
  | p :: ps, L, s, hok, h => by
    simp only [VG.Proof.ChaCha20.X86.Quad.loadsOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hk, hn, hr⟩, hok⟩ := hok
    rw [List.map_cons, ← List.singleton_append, WP.block_append_iff]
    exact WP.mono (VG.Proof.ChaCha20.X86.Quad.ld_ok hb hwb hk hn hr h) fun s₁ h₁ => VG.Proof.ChaCha20.X86.Quad.loads_ok ps _ s₁ hok h₁

theorem st_ok {L : VG.Proof.ChaCha20.X86.Quad.Loc} {vs : Nat → CState} {s : State} {r : XReg} {k : Nat} (hk : k < 16)
    (hs : L k = some r) (h : VG.Proof.ChaCha20.X86.Quad.RI buf L vs s₀ s) :
    WP isa (.block [VG.Impl.ChaCha20.X86.Xor.st k r]) s (VG.Proof.ChaCha20.X86.Quad.RI buf (VG.Proof.ChaCha20.X86.Quad.upd L k none) vs s₀) := by
  have e := (VG.Proof.ChaCha20.X86.Quad.ea_gpr h.gpr _).trans (hb (slot k) (by simp only [slot]; omega))
  have o : InRegions s.wr (buf + BitVec.ofNat 64 (slot k)) 16 := by
    rw [h.wr]; exact VG.Proof.ChaCha20.X86.Quad.out_buf hwb (by simp only [slot]; omega)
  apply WP.of_runBlock
  simp only [VG.Impl.ChaCha20.X86.Xor.st, runBlock_cons, runStep_some, runBlock_nil, exec, State.store128, e, o, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun j hj l hl => ?_, VG.Proof.ChaCha20.X86.Quad.slots_frame_write h.frame (List.mem_singleton_self _) _ hk, h.gpr,
    h.rd, h.wr⟩
  have hv := h.holds j hj l hl
  by_cases hjk : j = k
  · subst hjk
    rw [VG.Proof.ChaCha20.X86.Quad.val_none (show VG.Proof.ChaCha20.X86.Quad.upd L j none j = none from ite_eq_left rfl)]
    show (s.mem.writeW _ _).readW _ _ = _
    rw [VG.Proof.ChaCha20.X86.Quad.lane_self _ _ _ _ hl, ← hv, VG.Proof.ChaCha20.X86.Quad.val_some hs]
  · have hu : VG.Proof.ChaCha20.X86.Quad.upd L k none j = L j := ite_eq_right hjk
    rcases hL : L j with _ | r'
    · rw [VG.Proof.ChaCha20.X86.Quad.val_none (hu.trans hL)]
      show (s.mem.writeW _ _).readW _ _ = _
      rw [VG.Proof.ChaCha20.X86.Quad.lane_other _ _ _ hj hk hl (Ne.symm hjk), ← hv, VG.Proof.ChaCha20.X86.Quad.val_none hL]
    · rw [VG.Proof.ChaCha20.X86.Quad.val_some (hu.trans hL)]; rw [VG.Proof.ChaCha20.X86.Quad.val_some hL] at hv; exact hv

theorem stores_ok {vs : Nat → CState} : ∀ (ps : List (Nat × XReg)) (L : VG.Proof.ChaCha20.X86.Quad.Loc) (s : State),
    VG.Proof.ChaCha20.X86.Quad.storesOk L ps = true → VG.Proof.ChaCha20.X86.Quad.RI buf L vs s₀ s →
    WP isa (.block (ps.map fun p => VG.Impl.ChaCha20.X86.Xor.st p.1 p.2)) s (VG.Proof.ChaCha20.X86.Quad.RI buf (VG.Proof.ChaCha20.X86.Quad.storesLoc L ps) vs s₀)
  | [], _, _, _, h => WP.block_nil h
  | p :: ps, L, s, hok, h => by
    simp only [VG.Proof.ChaCha20.X86.Quad.storesOk, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hk, hs⟩, hok⟩ := hok
    rw [List.map_cons, ← List.singleton_append, WP.block_append_iff]
    exact WP.mono (VG.Proof.ChaCha20.X86.Quad.st_ok hb hwb hk hs h) fun s₁ h₁ => VG.Proof.ChaCha20.X86.Quad.stores_ok ps _ s₁ hok h₁

theorem quad_ok {k : Kernel} (K : VG.Proof.ChaCha20.X86.Quad.KernelOk k) (hinv : K.Inv buf s₀.mem) {L : VG.Proof.ChaCha20.X86.Quad.Loc} {q : QStep}
    {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16)
    (hw : w < 16) (hok : VG.Proof.ChaCha20.X86.Quad.quadOk L q x y z w = true) {vs : Nat → CState} {s : State}
    (h : VG.Proof.ChaCha20.X86.Quad.RI buf L vs s₀ s) :
    WP isa (.block (k.qr q.a q.b q.c q.d)) s
      (VG.Proof.ChaCha20.X86.Quad.RI buf L (fun l => qround (vs l) ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) := by
  simp only [VG.Proof.ChaCha20.X86.Quad.quadOk, decide_eq_true_eq] at hok
  obtain ⟨hLa, hLb, hLc, hLd, hab, hac, had, hbc, hbd, hcd, ha7, hb7, hc7, hd7, h7, ho⟩ := hok
  refine WP.mono (K.qr_ok hab hac had hbc hbd hcd ha7 hb7 hc7 hd7 s
      (fun e he => (VG.Proof.ChaCha20.X86.Quad.ea_gpr h.gpr _).trans (hb e he)) (h.wr ▸ hwb)
      (K.inv_frame hinv h.frame (by simpa using VG.Proof.ChaCha20.X86.Quad.kR_slots buf)))
    fun s' ⟨hv, hx', hg, hm, hr, hwr⟩ => ⟨fun k hk l hl => ?_, hm ▸ h.frame, hg.trans h.gpr,
      hr.trans h.rd, hwr.trans h.wr⟩
  obtain ⟨ea, eb, ec, ed⟩ := hv l hl
  have vx : VG.Proof.ChaCha20.X86.dw s q.a l = (vs l)[x] := by rw [← h.holds x hx l hl, VG.Proof.ChaCha20.X86.Quad.val_some hLa]
  have vy : VG.Proof.ChaCha20.X86.dw s q.b l = (vs l)[y] := by rw [← h.holds y hy l hl, VG.Proof.ChaCha20.X86.Quad.val_some hLb]
  have vz : VG.Proof.ChaCha20.X86.dw s q.c l = (vs l)[z] := by rw [← h.holds z hz l hl, VG.Proof.ChaCha20.X86.Quad.val_some hLc]
  have vw : VG.Proof.ChaCha20.X86.dw s q.d l = (vs l)[w] := by rw [← h.holds w hw l hl, VG.Proof.ChaCha20.X86.Quad.val_some hLd]
  rw [vx, vy, vz, vw] at ea eb ec ed
  rw [qround_get _ _ _ _ _ k hk]
  simp only
  by_cases e4 : w = k
  · subst e4; rw [ite_eq_left rfl, VG.Proof.ChaCha20.X86.Quad.val_some hLd]; exact ed
  by_cases e3 : z = k
  · subst e3; rw [ite_eq_right e4, ite_eq_left rfl, VG.Proof.ChaCha20.X86.Quad.val_some hLc]; exact ec
  by_cases e2 : y = k
  · subst e2; rw [ite_eq_right e4, ite_eq_right e3, ite_eq_left rfl, VG.Proof.ChaCha20.X86.Quad.val_some hLb]; exact eb
  by_cases e1 : x = k
  · subst e1; rw [ite_eq_right e4, ite_eq_right e3, ite_eq_right e2, ite_eq_left rfl, VG.Proof.ChaCha20.X86.Quad.val_some hLa]
    exact ea
  rw [ite_eq_right e4, ite_eq_right e3, ite_eq_right e2, ite_eq_right e1, ← h.holds k hk l hl]
  rcases hL : L k with _ | r
  · rw [VG.Proof.ChaCha20.X86.Quad.val_none hL, VG.Proof.ChaCha20.X86.Quad.val_none hL, hm]
  · obtain ⟨na, nb, nc, nd⟩ : L k ≠ some q.a ∧ L k ≠ some q.b ∧ L k ≠ some q.c ∧ L k ≠ some q.d := by
      rcases ho k hk with e | e | e | e | e
      · exact absurd e.symm e1
      · exact absurd e.symm e2
      · exact absurd e.symm e3
      · exact absurd e.symm e4
      · exact e
    rw [VG.Proof.ChaCha20.X86.Quad.val_some hL, VG.Proof.ChaCha20.X86.Quad.val_some hL, hx' r (fun e => na (by rw [hL, e])) (fun e => nb (by rw [hL, e]))
      (fun e => nc (by rw [hL, e])) (fun e => nd (by rw [hL, e])) (fun e => h7 k hk (by rw [hL, e]))]

theorem step_ok {k : Kernel} (K : VG.Proof.ChaCha20.X86.Quad.KernelOk k) (hinv : K.Inv buf s₀.mem) {L : VG.Proof.ChaCha20.X86.Quad.Loc} {q : QStep}
    {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16)
    (hw : w < 16) (hok : VG.Proof.ChaCha20.X86.Quad.stepOk L q x y z w = true) {vs : Nat → CState} {s : State}
    (h : VG.Proof.ChaCha20.X86.Quad.RI buf L vs s₀ s) :
    WP isa (.block (q.code k)) s
      (VG.Proof.ChaCha20.X86.Quad.RI buf (VG.Proof.ChaCha20.X86.Quad.stepLoc L q) (fun l => qround (vs l) ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) := by
  simp only [VG.Proof.ChaCha20.X86.Quad.stepOk, Bool.and_eq_true] at hok
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hok
  rw [QStep.code, WP.block_append_iff, WP.block_append_iff]
  exact WP.mono (VG.Proof.ChaCha20.X86.Quad.loads_ok hb hwb _ _ s h₁ h) fun s₁ r₁ =>
    WP.mono (VG.Proof.ChaCha20.X86.Quad.quad_ok hb hwb K hinv hx hy hz hw h₂ r₁) fun s₂ r₂ => VG.Proof.ChaCha20.X86.Quad.stores_ok hb hwb _ _ s₂ h₃ r₂

end

/-! ## Double rounds -/

/-- The quarter rounds of `plan`. -/
abbrev qs (i : Nat) : QStep := plan.getD i ⟨[], .xmm0, .xmm0, .xmm0, .xmm0, []⟩

/-- The loads of `cached`. -/
def enter : List (XReg × Nat) := cached.map fun p => (p.2, p.1)

/-- Where the words are between double rounds. -/
def loc₀ : VG.Proof.ChaCha20.X86.Quad.Loc := VG.Proof.ChaCha20.X86.Quad.loadsLoc (fun _ => none) VG.Proof.ChaCha20.X86.Quad.enter

/-- Where the words are before quarter round `i` of a double round. -/
def locs : Nat → VG.Proof.ChaCha20.X86.Quad.Loc
  | 0 => VG.Proof.ChaCha20.X86.Quad.loc₀
  | i + 1 => VG.Proof.ChaCha20.X86.Quad.stepLoc (VG.Proof.ChaCha20.X86.Quad.locs i) (VG.Proof.ChaCha20.X86.Quad.qs i)

theorem locs_8 : ∀ j, j < 16 → VG.Proof.ChaCha20.X86.Quad.locs 8 j = VG.Proof.ChaCha20.X86.Quad.loc₀ j := by decide

/-- The rounds invariant with every word in its slot. -/
abbrev RI4 (buf : Addr) (vs : Nat → CState) (s₀ s : State) : Prop := VG.Proof.ChaCha20.X86.Quad.RI buf (fun _ => none) vs s₀ s

section
variable {buf : Addr} {s₀ : State} (hb : ∀ d, d < 320 → s₀.ea (at_ .edi d) = buf + BitVec.ofNat 64 d)
  (hwb : VG.Proof.ChaCha20.X86.Quad.bufR buf ∈ s₀.wr)
include hb hwb

theorem doubleRound4_ok {k : Kernel} (K : VG.Proof.ChaCha20.X86.Quad.KernelOk k) (hinv : K.Inv buf s₀.mem) {vs : Nat → CState}
    {s : State} (h : VG.Proof.ChaCha20.X86.Quad.RI buf VG.Proof.ChaCha20.X86.Quad.loc₀ vs s₀ s) :
    WP isa (doubleRound4 k) s (VG.Proof.ChaCha20.X86.Quad.RI buf VG.Proof.ChaCha20.X86.Quad.loc₀ (fun l => innerBlock (vs l)) s₀) := by
  unfold doubleRound4
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Quad.step_ok hb hwb K hinv (L := VG.Proof.ChaCha20.X86.Quad.locs 0) (q := VG.Proof.ChaCha20.X86.Quad.qs 0) (x := 0) (y := 4) (z := 8) (w := 12)
    (by decide) (by decide) (by decide) (by decide) (by decide) h) fun _ h1 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Quad.step_ok hb hwb K hinv (L := VG.Proof.ChaCha20.X86.Quad.locs 1) (q := VG.Proof.ChaCha20.X86.Quad.qs 1) (x := 1) (y := 5) (z := 9) (w := 13)
    (by decide) (by decide) (by decide) (by decide) (by decide) h1) fun _ h2 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Quad.step_ok hb hwb K hinv (L := VG.Proof.ChaCha20.X86.Quad.locs 2) (q := VG.Proof.ChaCha20.X86.Quad.qs 2) (x := 2) (y := 6) (z := 10) (w := 14)
    (by decide) (by decide) (by decide) (by decide) (by decide) h2) fun _ h3 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Quad.step_ok hb hwb K hinv (L := VG.Proof.ChaCha20.X86.Quad.locs 3) (q := VG.Proof.ChaCha20.X86.Quad.qs 3) (x := 3) (y := 7) (z := 11) (w := 15)
    (by decide) (by decide) (by decide) (by decide) (by decide) h3) fun _ h4 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Quad.step_ok hb hwb K hinv (L := VG.Proof.ChaCha20.X86.Quad.locs 4) (q := VG.Proof.ChaCha20.X86.Quad.qs 4) (x := 0) (y := 5) (z := 10) (w := 15)
    (by decide) (by decide) (by decide) (by decide) (by decide) h4) fun _ h5 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Quad.step_ok hb hwb K hinv (L := VG.Proof.ChaCha20.X86.Quad.locs 5) (q := VG.Proof.ChaCha20.X86.Quad.qs 5) (x := 1) (y := 6) (z := 11) (w := 12)
    (by decide) (by decide) (by decide) (by decide) (by decide) h5) fun _ h6 => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Quad.step_ok hb hwb K hinv (L := VG.Proof.ChaCha20.X86.Quad.locs 6) (q := VG.Proof.ChaCha20.X86.Quad.qs 6) (x := 2) (y := 7) (z := 8) (w := 13)
    (by decide) (by decide) (by decide) (by decide) (by decide) h6) fun _ h7 => ?_)
  exact WP.mono (VG.Proof.ChaCha20.X86.Quad.step_ok hb hwb K hinv (L := VG.Proof.ChaCha20.X86.Quad.locs 7) (q := VG.Proof.ChaCha20.X86.Quad.qs 7) (x := 3) (y := 4) (z := 9) (w := 14)
    (by decide) (by decide) (by decide) (by decide) (by decide) h7) fun _ h8 => h8.congr VG.Proof.ChaCha20.X86.Quad.locs_8

theorem rounds4_ok {k : Kernel} (K : VG.Proof.ChaCha20.X86.Quad.KernelOk k) (hinv : K.Inv buf s₀.mem) {vs : Nat → CState}
    {s : State} (h : VG.Proof.ChaCha20.X86.Quad.RI buf VG.Proof.ChaCha20.X86.Quad.loc₀ vs s₀ s) :
    ∀ n, WP isa (rounds4 k n) s (VG.Proof.ChaCha20.X86.Quad.RI buf VG.Proof.ChaCha20.X86.Quad.loc₀ (fun l => Nat.repeat innerBlock n (vs l)) s₀)
  | 0 => WP.block_nil h
  | n + 1 => WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Quad.rounds4_ok K hinv h n) fun _ h' => VG.Proof.ChaCha20.X86.Quad.doubleRound4_ok hb hwb K hinv h')

omit hb hwb in
theorem enter_eq : cached.map (fun p => ld p.2 p.1) = enter.map fun p => ld p.1 p.2 := rfl

theorem rounds_ok {k : Kernel} (K : VG.Proof.ChaCha20.X86.Quad.KernelOk k) (hinv : K.Inv buf s₀.mem) {vs : Nat → CState}
    (h : VG.Proof.ChaCha20.X86.Quad.Holds4 buf vs s₀.mem) :
    WP isa (rounds10 k) s₀ (VG.Proof.ChaCha20.X86.Quad.RI4 buf (fun l => Nat.repeat innerBlock 10 (vs l)) s₀) := by
  unfold rounds10
  rw [VG.Proof.ChaCha20.X86.Quad.enter_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Quad.loads_ok hb hwb (vs := vs) VG.Proof.ChaCha20.X86.Quad.enter (fun _ => none) s₀ (by decide)
    ⟨h, Frame.refl _ _, rfl, rfl, rfl⟩) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Quad.rounds4_ok hb hwb K hinv h₁ 10) fun s₂ h₂ => ?_)
  exact WP.mono (VG.Proof.ChaCha20.X86.Quad.stores_ok hb hwb cached VG.Proof.ChaCha20.X86.Quad.loc₀ s₂ (by decide) h₂) fun _ h₃ => h₃.congr (by decide)

end

/-! ## The context -/

open VG.Spec.ChaCha20 (stateAt serialize)

/-- The state, 64 bytes at `st`. -/
abbrev stR (st : Addr) : Region := ⟨st, 64⟩

/-- Where `ebx` and `edi` point (`state` and `buf`), and what the code may
access there. -/
structure Ctx (st buf : Addr) (s : State) : Prop where
  eaS : ∀ d, d < 64 → s.ea (at_ .ebx d) = st + BitVec.ofNat 64 d
  eaB : ∀ d, d < 320 → s.ea (at_ .edi d) = buf + BitVec.ofNat 64 d
  wst : VG.Proof.ChaCha20.X86.Quad.stR st ∈ s.wr
  wb : VG.Proof.ChaCha20.X86.Quad.bufR buf ∈ s.wr
  sb : (VG.Proof.ChaCha20.X86.Quad.stR st).Disjoint (VG.Proof.ChaCha20.X86.Quad.bufR buf)

theorem Ctx.of {st buf : Addr} {s s' : State} (h : VG.Proof.ChaCha20.X86.Quad.Ctx st buf s) (hg : s'.gpr = s.gpr)
    (hw : s'.wr = s.wr) : VG.Proof.ChaCha20.X86.Quad.Ctx st buf s' :=
  ⟨fun d hd => (VG.Proof.ChaCha20.X86.Quad.ea_gpr hg _).trans (h.eaS d hd), fun d hd => (VG.Proof.ChaCha20.X86.Quad.ea_gpr hg _).trans (h.eaB d hd),
    hw ▸ h.wst, hw ▸ h.wb, h.sb⟩

theorem in_st {rs ws : List Region} {st : Addr} (hw : VG.Proof.ChaCha20.X86.Quad.stR st ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions (rs ++ ws) (st + BitVec.ofNat 64 d) n :=
  ⟨VG.Proof.ChaCha20.X86.Quad.stR st, List.mem_append_right _ hw, Offset.contains_base st h (by lit_omega)⟩

theorem out_st {ws : List Region} {st : Addr} (hw : VG.Proof.ChaCha20.X86.Quad.stR st ∈ ws) {d n : Nat} (h : d + n ≤ 64) :
    InRegions ws (st + BitVec.ofNat 64 d) n :=
  ⟨VG.Proof.ChaCha20.X86.Quad.stR st, hw, Offset.contains_base st h (by lit_omega)⟩

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (VG.Proof.ChaCha20.X86.Quad.stR p).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (Offset.contains_base p (by lit_omega) (by lit_omega)) hd (by decide)

/-- Doubleword `i` of row `r` of a state in memory. -/
theorem row_lane (m : Mem) (st : Addr) {r i : Nat} (hr : r < 4) (hi : i < 4) :
    dword (m.readW (st + BitVec.ofNat 64 (16 * r)) 128) i = (stateAt m st)[4 * r + i]'(by omega) := by
  rw [VG.Proof.ChaCha20.X86.Quad.lane_load _ _ _ hi]
  simp only [stateAt, Vector.getElem_ofFn]
  exact congrArg (fun d => m.readW (st + BitVec.ofNat 64 d) 32) (by omega)

theorem ctr_get (S : CState) (j : Nat) {k : Nat} (hk : k < 16) :
    (ctr S j)[k] = if k = 12 then S[12] + BitVec.ofNat 32 j else S[k] := by
  simp only [ctr, Vector.getElem_set]
  by_cases h : k = 12
  · subst h; simp
  · simp [h, Ne.symm h]

/-! ## The setup -/

/-- The words below `n` of the four states `vs` are in their slots, and only
the slots have been written since `s₀`. -/
structure Done (buf : Addr) (vs : Nat → CState) (n : Nat) (s₀ s : State) : Prop where
  done : ∀ k (hk : k < 16), k < n → ∀ l, l < 4 →
    s.mem.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 = (vs l)[k]
  frame : Frame [VG.Proof.ChaCha20.X86.Quad.slotsR buf] s₀.mem s.mem
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- Row `r` of the state `C`, in `xmm4`. -/
def Row4 (C : CState) (r : Nat) (s : State) : Prop :=
  ∀ i (hi : i < 4) (hr : r < 4), dword (s.xmm .xmm4) i = C[4 * r + i]'(by omega)

section
variable {st buf : Addr} {s₀ : State} (hc : VG.Proof.ChaCha20.X86.Quad.Ctx st buf s₀)
include hc

theorem setupWord_ok {r i : Nat} (hr : r < 4) (hi : i < 4) {s : State}
    (h : VG.Proof.ChaCha20.X86.Quad.Done buf (fun _ => stateAt s₀.mem st) (4 * r + i) s₀ s)
    (hx : VG.Proof.ChaCha20.X86.Quad.Row4 (stateAt s₀.mem st) r s) :
    WP isa (.block [bcast .xmm0 .xmm4 i, .movdquStore (at_ .edi (slot (4 * r + i))) .xmm0]) s
      fun s' => VG.Proof.ChaCha20.X86.Quad.Done buf (fun _ => stateAt s₀.mem st) (4 * r + (i + 1)) s₀ s' ∧
        VG.Proof.ChaCha20.X86.Quad.Row4 (stateAt s₀.mem st) r s' := by
  have e := (VG.Proof.ChaCha20.X86.Quad.ea_gpr h.gpr _).trans (hc.eaB (slot (4 * r + i)) (by simp only [slot]; omega))
  have o : InRegions s.wr (buf + BitVec.ofNat 64 (slot (4 * r + i))) 16 := by
    rw [h.wr]; exact VG.Proof.ChaCha20.X86.Quad.out_buf hc.wb (by simp only [slot]; omega)
  apply WP.of_runBlock
  simp only [bcast, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.store128,
    VG.Proof.ChaCha20.X86.Quad.ea_setXmm, e, RegUpd.wr_setXmm, o, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun k hk hkn l hl => ?_, ?_, ?_, ?_, ?_⟩, fun j hj hr' => ?_⟩
  · simp only [RegUpd.mem_setXmm]
    by_cases hke : k = 4 * r + i
    · subst hke
      rw [VG.Proof.ChaCha20.X86.Quad.lane_self _ _ _ _ hl, RegUpd.xmm_setXmm_self, dword_shufDwords_bcast _ hi hl,
        hx i hi hr]
    · rw [VG.Proof.ChaCha20.X86.Quad.lane_other _ _ _ hk (by omega) hl (Ne.symm hke)]
      exact h.done k hk (by omega) l hl
  · exact VG.Proof.ChaCha20.X86.Quad.slots_frame_write h.frame (List.mem_singleton_self _) _ (by omega)
  · exact h.gpr
  · exact h.rd
  · exact h.wr
  · simp only [RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true]; exact hx j hj hr'

theorem setupRow_ok {r : Nat} (hr : r < 4) {s : State}
    (h : VG.Proof.ChaCha20.X86.Quad.Done buf (fun _ => stateAt s₀.mem st) (4 * r) s₀ s) :
    WP isa (.block (setupRow r)) s (VG.Proof.ChaCha20.X86.Quad.Done buf (fun _ => stateAt s₀.mem st) (4 * r + 4) s₀) := by
  have e := (VG.Proof.ChaCha20.X86.Quad.ea_gpr h.gpr _).trans (hc.eaS (16 * r) (by omega))
  have i : InRegions (s.rd ++ s.wr) (st + BitVec.ofNat 64 (16 * r)) 16 := by
    rw [h.wr]; exact VG.Proof.ChaCha20.X86.Quad.in_st hc.wst (by omega)
  have hS : stateAt s.mem st = stateAt s₀.mem st := VG.Proof.ChaCha20.X86.Quad.stateAt_frame h.frame (by
    simp only [List.mem_singleton, forall_eq]
    exact hc.sb.sub_right (Region.sub_prefix (by lit_omega)))
  rw [setupRow, ← List.singleton_append, WP.block_append_iff]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, e, i, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  have h₀ : VG.Proof.ChaCha20.X86.Quad.Done buf (fun _ => stateAt s₀.mem st) (4 * r + 0) s₀
      (s.setXmm .xmm4 (s.mem.readW (st + BitVec.ofNat 64 (16 * r)) 128)) ∧
      VG.Proof.ChaCha20.X86.Quad.Row4 (stateAt s₀.mem st) r (s.setXmm .xmm4 (s.mem.readW (st + BitVec.ofNat 64 (16 * r)) 128)) :=
    ⟨⟨fun k hk hkn l hl => h.done k hk hkn l hl, h.frame, h.gpr, h.rd, h.wr⟩, fun j hj hr' => by
      rw [RegUpd.xmm_setXmm_self, VG.Proof.ChaCha20.X86.Quad.row_lane _ _ hr' hj, hS]⟩
  exact WP.mono (wp_range_flatMap (M := isa)
    (fun i s => VG.Proof.ChaCha20.X86.Quad.Done buf (fun _ => stateAt s₀.mem st) (4 * r + i) s₀ s ∧ VG.Proof.ChaCha20.X86.Quad.Row4 (stateAt s₀.mem st) r s)
    (fun i s hi hs => VG.Proof.ChaCha20.X86.Quad.setupWord_ok hc hr hi hs.1 hs.2) 4 (Nat.le_refl _) _ h₀) fun _ h' => h'.1

/-- The counters `c + l` (from word 12 of `C`) at `ctrOff`. -/
def Ctrs (buf : Addr) (C : CState) (n : Nat) (m : Mem) : Prop :=
  ∀ l, l < n → m.readW (buf + BitVec.ofNat 64 (ctrOff + 4 * l)) 32 = C[12] + BitVec.ofNat 32 l

/-- `buf[272, 288)`, the counters. -/
abbrev ctrR (buf : Addr) : Region := ⟨buf + BitVec.ofNat 64 ctrOff, 16⟩

/-- Before lane `n` of the counters. -/
structure CI (buf : Addr) (C : CState) (n : Nat) (s₀ s : State) : Prop where
  slots : ∀ k (hk : k < 16) l, l < 4 → (k ≠ 12 ∨ l < n) →
    s.mem.readW (buf + BitVec.ofNat 64 (16 * k + 4 * l)) 32 = (ctr C l)[k]
  ctrs : VG.Proof.ChaCha20.X86.Quad.Ctrs buf C n s.mem
  eax : s.gpr .eax = C[12] + BitVec.ofNat 32 n
  frame : Frame [VG.Proof.ChaCha20.X86.Quad.slotsR buf, VG.Proof.ChaCha20.X86.Quad.ctrR buf] s₀.mem s.mem
  keep : ∀ r, r ≠ .eax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

omit hc in
theorem w32_other (m : Mem) (buf : Addr) (v : BitVec 32) {d e : Nat} (hd : d + 4 ≤ 2 ^ 32)
    (he : e + 4 ≤ 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (buf + BitVec.ofNat 64 e) v).readW (buf + BitVec.ofNat 64 d) 32 =
      m.readW (buf + BitVec.ofNat 64 d) 32 :=
  Mem.readW_writeW_sep (Offset.sep buf h (by lit_omega) (by lit_omega)) (by decide)

theorem ctrLane_ok {C : CState} {l : Nat} (hl : l < 4) {s : State} (h : VG.Proof.ChaCha20.X86.Quad.CI buf C l s₀ s) :
    WP isa (.block (ctrLane l)) s (VG.Proof.ChaCha20.X86.Quad.CI buf C (l + 1) s₀) := by
  have hdi : s.gpr .edi = s₀.gpr .edi := h.keep _ (by decide)
  have e₁ : VG.X86.addr (s₀.gpr .edi) (slot 12 + 4 * l) = buf + BitVec.ofNat 64 (16 * 12 + 4 * l) :=
    hc.eaB _ (by simp only [slot]; omega)
  have e₂ : VG.X86.addr (s₀.gpr .edi) (ctrOff + 4 * l) = buf + BitVec.ofNat 64 (ctrOff + 4 * l) :=
    hc.eaB _ (by simp only [ctrOff]; omega)
  have o₁ : InRegions s.wr (VG.X86.addr (s₀.gpr .edi) (slot 12 + 4 * l)) 4 := by
    rw [e₁, h.wr]; exact VG.Proof.ChaCha20.X86.Quad.out_buf hc.wb (by omega)
  refine Wp.wp_stm hdi o₁ fun s₁ u₁ => ?_
  have o₂ : InRegions s₁.wr (VG.X86.addr (s₀.gpr .edi) (ctrOff + 4 * l)) 4 := by
    rw [e₂, u₁.wr, h.wr]; exact VG.Proof.ChaCha20.X86.Quad.out_buf hc.wb (by simp only [ctrOff]; omega)
  refine Wp.wp_stm (by rw [u₁.gpr, hdi]) o₂ fun s₂ u₂ => ?_
  refine Wp.wp_addi fun s₃ u₃ => WP.block_nil ?_
  have hm : s₃.mem = (s.mem.writeW (buf + BitVec.ofNat 64 (16 * 12 + 4 * l)) (s.gpr .eax)).writeW
      (buf + BitVec.ofNat 64 (ctrOff + 4 * l)) (s.gpr .eax) := by
    rw [u₃.mem, u₂.mem, u₁.mem, u₁.gpr, e₁, e₂]
  refine ⟨fun k hk l' hl' hkl => ?_, fun l' hl' => ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [hm, VG.Proof.ChaCha20.X86.Quad.w32_other (d := 16 * k + 4 * l') (e := ctrOff + 4 * l) _ _ _ (by lit_omega) (by simp only [ctrOff]; lit_omega)
      (by simp only [ctrOff]; omega)]
    by_cases he : k = 12 ∧ l' = l
    · obtain ⟨rfl, rfl⟩ := he
      rw [Mem.readW_writeW_self32, h.eax, VG.Proof.ChaCha20.X86.Quad.ctr_get _ _ hk, ite_eq_left rfl]
    · rw [VG.Proof.ChaCha20.X86.Quad.w32_other (d := 16 * k + 4 * l') (e := 16 * 12 + 4 * l) _ _ _ (by lit_omega) (by lit_omega) (by omega)]
      exact h.slots k hk l' hl' (by omega)
  · rw [hm]
    by_cases he : l' = l
    · subst he; rw [Mem.readW_writeW_self32, h.eax]
    · rw [VG.Proof.ChaCha20.X86.Quad.w32_other (d := ctrOff + 4 * l') (e := ctrOff + 4 * l) _ _ _ (by simp only [ctrOff]; lit_omega) (by simp only [ctrOff]; lit_omega)
        (by simp only [ctrOff]; omega),
        VG.Proof.ChaCha20.X86.Quad.w32_other (d := ctrOff + 4 * l') (e := 16 * 12 + 4 * l) _ _ _ (by simp only [ctrOff]; lit_omega) (by lit_omega)
        (by simp only [ctrOff]; omega)]
      exact h.ctrs l' (by omega)
  · rw [u₃.gpr, u₂.gpr, u₁.gpr, h.eax, Offset.add_ofNat_add_one]
  · rw [hm]
    refine (h.frame.writeW (List.mem_cons_self ..) _ (Offset.contains_base buf (by omega) (by lit_omega))).writeW
      (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ ?_
    exact Offset.contains buf (by omega) (by omega) (by simp only [ctrOff]; lit_omega)
  · rw [u₃.other r hr, u₂.gpr, u₁.gpr, h.keep r hr]
  · rw [u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₃.wr, u₂.wr, u₁.wr, h.wr]

/-- What the setup leaves: the four states in the slots, the counters at
`ctrOff`, and everything else as it was (but `eax`). -/
structure SPost (buf : Addr) (C : CState) (s₀ s : State) : Prop where
  holds : VG.Proof.ChaCha20.X86.Quad.Holds4 buf (fun l => ctr C l) s.mem
  ctrs : VG.Proof.ChaCha20.X86.Quad.Ctrs buf C 4 s.mem
  frame : Frame [VG.Proof.ChaCha20.X86.Quad.slotsR buf, VG.Proof.ChaCha20.X86.Quad.ctrR buf] s₀.mem s.mem
  keep : ∀ r, r ≠ .eax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem setup4_ok : WP isa (.block setup4) s₀ (VG.Proof.ChaCha20.X86.Quad.SPost buf (stateAt s₀.mem st) s₀) := by
  rw [setup4, WP.block_append_iff]
  refine WP.mono (wp_range_flatMap (M := isa) (fun r s => VG.Proof.ChaCha20.X86.Quad.Done buf (fun _ => stateAt s₀.mem st) (4 * r) s₀ s)
    (fun r s hr hs => VG.Proof.ChaCha20.X86.Quad.setupRow_ok hc hr hs) 4 (Nat.le_refl _) s₀
    ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, rfl, rfl, rfl⟩) fun s h => ?_
  have hb : s.gpr .ebx = s₀.gpr .ebx := by rw [h.gpr]
  have e : VG.X86.addr (s₀.gpr .ebx) 48 = st + BitVec.ofNat 64 48 := hc.eaS 48 (by decide)
  have hS : stateAt s.mem st = stateAt s₀.mem st := VG.Proof.ChaCha20.X86.Quad.stateAt_frame h.frame (by
    simp only [List.mem_singleton, forall_eq]
    exact hc.sb.sub_right (Region.sub_prefix (by lit_omega)))
  have v : s.mem.readW (st + BitVec.ofNat 64 48) 32 = (stateAt s₀.mem st)[12] := by
    rw [← hS]; simp [stateAt]
  rw [setupCtr, ← List.singleton_append]
  refine Wp.wp_ldm hb (by rw [e, h.rd, h.wr]; exact VG.Proof.ChaCha20.X86.Quad.in_st hc.wst (by decide)) fun s₁ u₁ => ?_
  rw [e, v] at u₁
  have c₀ : VG.Proof.ChaCha20.X86.Quad.CI buf (stateAt s₀.mem st) 0 s₀ s₁ :=
    ⟨fun k hk l hl hkl => by
      have hk12 : k ≠ 12 := by omega
      rw [u₁.mem, h.done k hk (by omega) l hl, VG.Proof.ChaCha20.X86.Quad.ctr_get _ _ hk, ite_eq_right hk12],
      fun _ h => absurd h (Nat.not_lt_zero _), by rw [u₁.gpr]; simp,
      by rw [u₁.mem]; exact h.frame.mono (by simp), fun r hr => by rw [u₁.other r hr, h.gpr],
      by rw [u₁.rd, h.rd], by rw [u₁.wr, h.wr]⟩
  refine WP.mono (wp_range_flatMap (M := isa) (fun l s => VG.Proof.ChaCha20.X86.Quad.CI buf (stateAt s₀.mem st) l s₀ s)
    (fun l s hl hs => VG.Proof.ChaCha20.X86.Quad.ctrLane_ok hc hl hs) 4 (Nat.le_refl _) s₁ c₀) fun s' h' => ?_
  exact ⟨fun k hk l hl => h'.slots k hk l hl (by omega), h'.ctrs, h'.frame, h'.keep, h'.rd, h'.wr⟩

end

/-! ## The output: loading a row -/

theorem xr_ne : ∀ i, i < 4 → ∀ j, j < 4 → i ≠ j → xr i ≠ xr j := by decide
theorem xr_ne45 : ∀ i, i < 4 → xr i ≠ .xmm4 ∧ xr i ≠ .xmm5 := by decide

/-- Words `4 r, …, 4 r + 3` of the four states `vs` are in their slots. -/
def RowHolds (buf : Addr) (vs : Nat → CState) (r : Nat) (m : Mem) : Prop :=
  ∀ i (hi : i < 4) (hr : r < 4) l, l < 4 →
    m.readW (buf + BitVec.ofNat 64 (16 * (4 * r + i) + 4 * l)) 32 = (vs l)[4 * r + i]'(by omega)

theorem loadRow_ok {st buf : Addr} {r : Nat} (hr : r < 4) {vs : Nat → CState} {s : State}
    (hc : VG.Proof.ChaCha20.X86.Quad.Ctx st buf s) (hh : VG.Proof.ChaCha20.X86.Quad.RowHolds buf vs r s.mem) :
    WP isa (.block (loadRow r)) s fun s' =>
      (∀ i (hi : i < 4) l, l < 4 → dword (s'.xmm (xr i)) l = (vs l)[4 * r + i]) ∧
      VG.Proof.ChaCha20.X86.Quad.Row4 (stateAt s.mem st) r s' ∧ s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e0 := hc.eaB (slot (4 * r)) (by simp only [slot]; omega)
  have e1 := hc.eaB (slot (4 * r + 1)) (by simp only [slot]; omega)
  have e2 := hc.eaB (slot (4 * r + 2)) (by simp only [slot]; omega)
  have e3 := hc.eaB (slot (4 * r + 3)) (by simp only [slot]; omega)
  have e4 := hc.eaS (16 * r) (by omega)
  have i0 := VG.Proof.ChaCha20.X86.Quad.in_buf (rs := s.rd) hc.wb (d := slot (4 * r)) (n := 16) (by simp only [slot]; omega)
  have i1 := VG.Proof.ChaCha20.X86.Quad.in_buf (rs := s.rd) hc.wb (d := slot (4 * r + 1)) (n := 16) (by simp only [slot]; omega)
  have i2 := VG.Proof.ChaCha20.X86.Quad.in_buf (rs := s.rd) hc.wb (d := slot (4 * r + 2)) (n := 16) (by simp only [slot]; omega)
  have i3 := VG.Proof.ChaCha20.X86.Quad.in_buf (rs := s.rd) hc.wb (d := slot (4 * r + 3)) (n := 16) (by simp only [slot]; omega)
  have i4 := VG.Proof.ChaCha20.X86.Quad.in_st (rs := s.rd) hc.wst (d := 16 * r) (n := 16) (by omega)
  apply WP.of_runBlock
  simp only [loadRow, runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, VG.Proof.ChaCha20.X86.Quad.ea_setXmm,
    e0, e1, e2, e3, e4, i0, i1, i2, i3, i4, ite_true, RegUpd.mem_setXmm, RegUpd.rd_setXmm,
    RegUpd.wr_setXmm, RegUpd.gpr_setXmm, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun i hi l hl => ?_, fun j hj hr' => ?_, trivial, trivial, trivial, trivial⟩
  · rcases cases4 hi with rfl | rfl | rfl | rfl <;>
      simp only [xr, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true] <;>
      rw [VG.Proof.ChaCha20.X86.Quad.lane_load _ _ _ hl]
    · exact hh 0 (by decide) hr l hl
    · exact hh 1 (by decide) hr l hl
    · exact hh 2 (by decide) hr l hl
    · exact hh 3 (by decide) hr l hl
  · simp only [RegUpd.xmm_setXmm_self]; exact VG.Proof.ChaCha20.X86.Quad.row_lane _ _ hr' hj

/-! ## Adding the input states -/

/-- While adding the input states to row `r`: `xr j` holds words `4 r + j`
of the four states `vs`, plus those of the input states `ctr C l` if
`j < i`; `xmm4` holds row `r` of `C`; nothing else has changed since `s₁`
(but XMM registers). -/
structure AW (vs : Nat → CState) (C : CState) (r i : Nat) (s₁ s : State) : Prop where
  regs : ∀ j (hj : j < 4) (hr : r < 4) l, l < 4 → dword (s.xmm (xr j)) l =
    if j < i then (vs l)[4 * r + j] + (ctr C l)[4 * r + j] else (vs l)[4 * r + j]
  row : VG.Proof.ChaCha20.X86.Quad.Row4 C r s
  mem : s.mem = s₁.mem
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr

theorem addWord_ok {st buf : Addr} {vs : Nat → CState} {C : CState} {r i : Nat} (hr : r < 4)
    (hi : i < 4) {s₁ s : State} (hc : VG.Proof.ChaCha20.X86.Quad.Ctx st buf s₁) (hct : VG.Proof.ChaCha20.X86.Quad.Ctrs buf C 4 s₁.mem)
    (h : VG.Proof.ChaCha20.X86.Quad.AW vs C r i s₁ s) : WP isa (.block (addWord4 r i)) s (VG.Proof.ChaCha20.X86.Quad.AW vs C r (i + 1) s₁) := by
  -- The value added to `xr i`: word `4 r + i` of the input states.
  suffices hadd : WP isa (.block (addWord4 r i)) s fun s' =>
      (∀ l, l < 4 → dword (s'.xmm (xr i)) l = dword (s.xmm (xr i)) l + (ctr C l)[4 * r + i]) ∧
      (∀ x, x ≠ xr i → x ≠ .xmm5 → s'.xmm x = s.xmm x) ∧
      s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr by
    refine WP.mono hadd fun s' ⟨ha, ho, hm, hg, hrd, hwr⟩ => ⟨fun j hj _ l hl => ?_, fun j hj hr' => ?_,
      hm.trans h.mem, hg.trans h.gpr, hrd.trans h.rd, hwr.trans h.wr⟩
    · by_cases hji : j = i
      · subst hji
        rw [ha l hl, h.regs j hj hr l hl, ite_eq_right (Nat.lt_irrefl j), ite_eq_left (Nat.lt_succ_self j)]
      · rw [ho _ (VG.Proof.ChaCha20.X86.Quad.xr_ne j hj i hi hji) (VG.Proof.ChaCha20.X86.Quad.xr_ne45 j hj).2, h.regs j hj hr l hl]
        by_cases hj' : j < i
        · rw [ite_eq_left hj', ite_eq_left (by omega)]
        · rw [ite_eq_right hj', ite_eq_right (by omega)]
    · rw [ho _ (VG.Proof.ChaCha20.X86.Quad.xr_ne45 i hi).1.symm (by decide)]; exact h.row j hj hr'
  have hgx := VG.Proof.ChaCha20.X86.Quad.xr_ne45 i hi
  by_cases h3 : r = 3 ∧ i = 0
  · obtain ⟨rfl, rfl⟩ := h3
    have e := (VG.Proof.ChaCha20.X86.Quad.ea_gpr h.gpr _).trans (hc.eaB ctrOff (by decide))
    have i5 : InRegions (s.rd ++ s.wr) (buf + BitVec.ofNat 64 ctrOff) 16 := by
      rw [h.rd, h.wr]; exact VG.Proof.ChaCha20.X86.Quad.in_buf hc.wb (by decide)
    rw [show addWord4 3 0 = [.movdquLoad .xmm5 (at_ .edi ctrOff), xb .paddd .xmm0 .xmm5] from rfl]
    apply WP.of_runBlock
    simp only [xb, xr, runBlock_cons, runStep_some, runBlock_nil, exec,
      XOp.exec, State.load128, e, i5, ite_true, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
      RegUpd.gpr_setXmm, Option.map_some, Option.some.injEq, exists_eq_left']
    refine ⟨fun l hl => ?_, fun x h0 h5 => ?_, trivial, trivial, trivial, trivial⟩
    · simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq, not_false_eq_true,
        dword_paddd _ _ hl]
      rw [VG.Proof.ChaCha20.X86.Quad.lane_load _ _ _ hl, h.mem, hct l hl, VG.Proof.ChaCha20.X86.Quad.ctr_get _ _ (by decide), ite_eq_left rfl]
    · simp only [RegUpd.xmm_setXmm_of_ne, h0, h5, not_false_eq_true]
  · apply WP.of_runBlock
    simp only [addWord4, h3, ite_false, xb, bcast, runBlock_cons, runStep_some, runBlock_nil, exec,
      XOp.exec, RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.gpr_setXmm,
      Option.some.injEq, exists_eq_left']
    refine ⟨fun l hl => ?_, fun x h0 h5 => ?_, trivial, trivial, trivial, trivial⟩
    · rw [RegUpd.xmm_setXmm_self, dword_paddd _ _ hl, RegUpd.xmm_setXmm_of_ne _ _ hgx.2,
        RegUpd.xmm_setXmm_self, dword_shufDwords_bcast _ hi hl, h.row i hi hr,
        VG.Proof.ChaCha20.X86.Quad.ctr_get _ _ (by omega), ite_eq_right (by omega)]
    · rw [RegUpd.xmm_setXmm_of_ne _ _ h0, RegUpd.xmm_setXmm_of_ne _ _ h5]

/-! ## Transposing -/

theorem transpose_ok (s : State) :
    WP isa (.block transpose) s fun s' =>
      (∀ l, l < 4 → ∀ j, j < 4 → dword (s'.xmm (outReg l)) j = dword (s.xmm (xr j)) l) ∧
      s'.mem = s.mem ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [transpose, xb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.gpr_setXmm,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl j hj => ?_, trivial, trivial, trivial, trivial⟩
  rcases cases4 hl with rfl | rfl | rfl | rfl <;>
    simp only [outReg, xr, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, reduceCtorEq,
      not_false_eq_true, eval_movdqa, punpcklqdq_eq, punpckhqdq_eq, punpckldq_eq, punpckhdq_eq,
      dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3] <;>
    rcases cases4 hj with rfl | rfl | rfl | rfl <;>
    simp only [dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2, dword_ofDwords_3]

/-! ## XORing 16 bytes into the data -/

/-- The data of one iteration: `W ≤ 256` bytes. -/
abbrev dW (a : Addr) (W : Nat) : Region := ⟨a, W⟩

/-- `buf[0, 16)`, where the keystream for the last bytes of the data is
stored: by then, the code has read the slot. -/
abbrev stashR (buf : Addr) : Region := ⟨buf, 16⟩

/-- Where `esi` points (the data of the iteration, `W` bytes), and that the
code may write it. -/
structure DCtx (a : Addr) (W : Nat) (s : State) : Prop where
  eaD : ∀ d, d < W → s.ea (at_ .esi d) = a + BitVec.ofNat 64 d
  wd : ∀ off n, off + n ≤ W → InRegions s.wr (a + BitVec.ofNat 64 off) n

theorem DCtx.of {a : Addr} {W : Nat} {s s' : State} (h : VG.Proof.ChaCha20.X86.Quad.DCtx a W s) (hg : s'.gpr = s.gpr)
    (hw : s'.wr = s.wr) : VG.Proof.ChaCha20.X86.Quad.DCtx a W s' :=
  ⟨fun d hd => (VG.Proof.ChaCha20.X86.Quad.ea_gpr hg _).trans (h.eaD d hd), fun off n h' => hw ▸ h.wd off n h'⟩

theorem xor16_ok {x : XReg} (hx : x ≠ .xmm6) {W off : Nat} (hW : W ≤ 256) (ho : off + 16 ≤ W) {a : Addr}
    {s : State} (hd : VG.Proof.ChaCha20.X86.Quad.DCtx a W s) :
    WP isa (.block (xor16 x off)) s fun s' =>
      (∀ k, k < W → s'.mem (a + BitVec.ofNat 64 k) = if off ≤ k ∧ k < off + 16 then
        s.mem (a + BitVec.ofNat 64 k) ^^^ (s.xmm x).extractLsb' (8 * (k - off)) 8
        else s.mem (a + BitVec.ofNat 64 k)) ∧
      Frame [VG.Proof.ChaCha20.X86.Quad.dW a W] s.mem s'.mem ∧ (∀ r, r ≠ .xmm6 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e := hd.eaD off (by omega)
  have o : InRegions s.wr (a + BitVec.ofNat 64 off) 16 := hd.wd off 16 ho
  have i : InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 off) 16 :=
    let ⟨r, hr, hc⟩ := o; ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.of_runBlock
  simp only [xor16, xb, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, State.load128,
    State.store128, VG.Proof.ChaCha20.X86.Quad.ea_setXmm, e, i, RegUpd.wr_setXmm, o, ite_true, RegUpd.mem_setXmm,
    RegUpd.gpr_setXmm, RegUpd.rd_setXmm, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun k hk => ?_, (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base a ho (by lit_omega)), fun r hr => ?_, trivial, trivial, trivial⟩
  · rw [VG.Proof.ChaCha20.X86.Bytes.byte_write16 _ _ _ (by omega) (by omega)]
    by_cases h : off ≤ k ∧ k < off + 16
    · rw [ite_eq_left h, ite_eq_left h]
      simp only [RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne _ _ hx, XBinOp.eval]
      rw [BitVec.extractLsb'_xor, byte_readW _ _ (by omega), Offset.add_add, Nat.add_sub_cancel' h.1]
    · rw [ite_eq_right h, ite_eq_right h]
  · rw [RegUpd.xmm_setXmm_of_ne _ _ hr, RegUpd.xmm_setXmm_of_ne _ _ hr]

/-! ## The 16 bytes of keystream of a register -/

theorem outReg_ne6 : ∀ l, l < 4 → outReg l ≠ .xmm6 := by decide

/-- Byte `k % 64` of a serialized state, in row `r`. -/
theorem serialize_row (S : CState) {k r : Nat} (hk : k % 64 / 16 = r) :
    (serialize S).getD (k % 64) 0 =
      (S[4 * r + k % 16 / 4]'(by omega)).extractLsb' (8 * (k % 16 % 4)) 8 := by
  rw [serialize_getD _ (Nat.mod_lt _ (by decide)), getElem_congr_idx (show k % 64 / 4 = 4 * r + k % 16 / 4 by omega),
    show k % 64 % 4 = k % 16 % 4 by omega]

/-- Byte `k` of the keystream of the four blocks `B`. -/
abbrev ksb (B : Nat → CState) (k : Nat) : Byte := (serialize (B (k / 64))).getD (k % 64) 0

/-- Byte `t` of a register holding row `r` of block `l` is byte `64 l + 16 r + t` of the keystream. -/
theorem reg_byte {B : Nat → CState} {r l : Nat} (hr : r < 4) {v : BitVec 128}
    (hv : ∀ j (hj : j < 4), dword v j = (B l)[4 * r + j]'(by omega)) {t : Nat} (ht : t < 16) :
    v.extractLsb' (8 * t) 8 = VG.Proof.ChaCha20.X86.Quad.ksb B (64 * l + 16 * r + t) := by
  have e₁ : (64 * l + 16 * r + t) / 64 = l := by omega
  have e₂ : (64 * l + 16 * r + t) % 64 / 16 = r := by omega
  have e₃ : (64 * l + 16 * r + t) % 16 = t := by omega
  rw [VG.Proof.ChaCha20.X86.Quad.ksb, e₁, VG.Proof.ChaCha20.X86.Quad.serialize_row _ e₂]
  simp only [e₃]
  rw [byte_dword, hv _ (by omega)]

/-! ## A chunk of 16 bytes -/

/-- The 16 bytes of data at `k / 16` are all within the `W` bytes. -/
abbrev Full (W k : Nat) : Prop := 16 * (k / 16) + 16 ≤ W

/-- Where the 16 bytes that run past the end of the data start, if any. -/
abbrev sOff (W : Nat) : Nat := W / 16 * 16

/-- The keystream for the bytes past the last 16-byte boundary of the data,
if there are any and the 16 bytes from that boundary are `done`, is in
`buf[0, 16)`. -/
def Stashed (buf : Addr) (B : Nat → CState) (W : Nat) (done : Nat → Prop) (m : Mem) : Prop :=
  W % 16 ≠ 0 → done (VG.Proof.ChaCha20.X86.Quad.sOff W) → ∀ i, i < W % 16 → m (buf + BitVec.ofNat 64 i) = VG.Proof.ChaCha20.X86.Quad.ksb B (VG.Proof.ChaCha20.X86.Quad.sOff W + i)

/-- While XORing row `r` of the four blocks `B` into `W` bytes of data: the
blocks below `l` are done, the registers `outReg l'` hold row `r` of the
blocks, and only the data and `buf[0, 16)` have been written since `s₁`. -/
structure XO (a buf : Addr) (B : Nat → CState) (W r l : Nat) (s₁ s : State) : Prop where
  data : ∀ k, k < W → s.mem (a + BitVec.ofNat 64 k) =
    if k % 64 / 16 = r ∧ k / 64 < l ∧ VG.Proof.ChaCha20.X86.Quad.Full W k then
      s₁.mem (a + BitVec.ofNat 64 k) ^^^ VG.Proof.ChaCha20.X86.Quad.ksb B k
    else s₁.mem (a + BitVec.ofNat 64 k)
  stash : VG.Proof.ChaCha20.X86.Quad.Stashed buf B W (fun o => o % 64 / 16 < r ∨ (o % 64 / 16 = r ∧ o / 64 < l)) s.mem
  regs : ∀ l', l' < 4 → ∀ j (hj : j < 4) (hr : r < 4), dword (s.xmm (outReg l')) j = (B l')[4 * r + j]
  frame : Frame [VG.Proof.ChaCha20.X86.Quad.dW a W, VG.Proof.ChaCha20.X86.Quad.stashR buf] s₁.mem s.mem
  gpr : s.gpr = s₁.gpr
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr

theorem toNat_ofNat32 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

section Chunk
variable {a buf : Addr} {B : Nat → CState} {W n : Nat} (hn : n < 2 ^ 32) (hW : W = min n 256)
  {s₁ : State} (hd : VG.Proof.ChaCha20.X86.Quad.DCtx a W s₁) (hbe : s₁.ea (at_ .edi 0) = buf + BitVec.ofNat 64 0)
  (hwb : VG.Proof.ChaCha20.X86.Quad.bufR buf ∈ s₁.wr) (hdb : (VG.Proof.ChaCha20.X86.Quad.dW a W).Disjoint (VG.Proof.ChaCha20.X86.Quad.stashR buf))
  (hebp : s₁.gpr .ebp = BitVec.ofNat 32 n)
include hn hW hd hbe hwb hdb hebp

omit hn hW hd hbe hwb hebp in
/-- The bytes of `buf[0, 16)` are outside the data. -/
theorem stash_out {i : Nat} (hi : i < 16) : ∀ r ∈ [VG.Proof.ChaCha20.X86.Quad.dW a W], ¬ r.Contains (buf + BitVec.ofNat 64 i) 1 := by
  intro r hr hc
  simp only [List.mem_singleton] at hr; subst hr
  exact hdb _ hc (Offset.contains_base buf (by omega) (by lit_omega))

theorem chunk_ok {r l : Nat} (hr : r < 4) (hl : l < 4) {s : State} (h : VG.Proof.ChaCha20.X86.Quad.XO a buf B W r l s₁ s) :
    WP isa (VG.Impl.ChaCha20.X86.Xor.chunk (outReg l) (chunkOff r l)) s (VG.Proof.ChaCha20.X86.Quad.XO a buf B W r (l + 1) s₁) := by
  have hW256 : W ≤ 256 := by omega
  have hgb : s.gpr .ebp = BitVec.ofNat 32 n := by rw [h.gpr, hebp]
  have ho : chunkOff r l + 16 ≤ 256 := by simp only [chunkOff]; omega
  have hreg := h.regs l hl
  unfold VG.Impl.ChaCha20.X86.Xor.chunk
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Bytes.cmpi_ok s .ebp _) fun s₂ ⟨g₂, m₂, x₂, r₂, w₂, c₂⟩ => ?_)
  rw [hgb, VG.Proof.ChaCha20.X86.Quad.toNat_ofNat32 hn, VG.Proof.ChaCha20.X86.Quad.toNat_ofNat32 (by omega)] at c₂
  refine WP.ite (decide (n < chunkOff r l + 16)) (by simp only [eval, c₂]) (fun hlt => ?_) (fun hge => ?_)
  · simp only [decide_eq_true_eq] at hlt
    refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Bytes.cmpi_ok s₂ .ebp _) fun s₃ ⟨g₃, m₃, x₃, r₃, w₃, c₃⟩ => ?_)
    rw [g₂, hgb, VG.Proof.ChaCha20.X86.Quad.toNat_ofNat32 hn, VG.Proof.ChaCha20.X86.Quad.toNat_ofNat32 (by omega)] at c₃
    refine WP.ite (decide (n < chunkOff r l + 1)) (by simp only [eval, c₃]) (fun hle => ?_) (fun hgt => ?_)
    · -- Past the end of the data: nothing.
      simp only [decide_eq_true_eq] at hle
      refine WP.block_nil ⟨fun k hk => ?_, fun hz hdn i hi => ?_, fun l' hl' j hj hr' => ?_, ?_, ?_, ?_, ?_⟩
      · rw [m₃, m₂, h.data k hk]
        by_cases c : k % 64 / 16 = r ∧ k / 64 < l ∧ VG.Proof.ChaCha20.X86.Quad.Full W k
        · rw [ite_eq_left c, ite_eq_left ⟨c.1, by omega, c.2.2⟩]
        · rw [ite_eq_right c, ite_eq_right (by simp only [VG.Proof.ChaCha20.X86.Quad.Full, chunkOff] at *; omega)]
      · rw [m₃, m₂]
        exact h.stash hz (by simp only [VG.Proof.ChaCha20.X86.Quad.sOff, chunkOff] at *; omega) i hi
      · rw [x₃, x₂]; exact h.regs l' hl' j hj hr'
      · rw [m₃, m₂]; exact h.frame
      · rw [g₃, g₂, h.gpr]
      · rw [r₃, r₂, h.rd]
      · rw [w₃, w₂, h.wr]
    · -- The last bytes of the data: the 16 bytes of keystream into `buf[0, 16)`.
      simp only [decide_eq_false_iff_not, Nat.not_lt] at hgt
      have hWn : W = n := by simp only [chunkOff] at *; omega
      have e : s₃.ea (at_ .edi 0) = buf + BitVec.ofNat 64 0 := by
        rw [VG.Proof.ChaCha20.X86.Quad.ea_gpr g₃, VG.Proof.ChaCha20.X86.Quad.ea_gpr g₂, VG.Proof.ChaCha20.X86.Quad.ea_gpr h.gpr, hbe]
      have o : InRegions s₃.wr (buf + BitVec.ofNat 64 0) 16 := by
        rw [w₃, w₂, h.wr]; exact VG.Proof.ChaCha20.X86.Quad.out_buf hwb (by decide)
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store128, e, o, ite_true,
        Option.some.injEq, exists_eq_left']
      have hm : ∀ k, k < W → (s₃.mem.writeW (buf + BitVec.ofNat 64 0) (s₃.xmm (outReg l)))
          (a + BitVec.ofNat 64 k) = s.mem (a + BitVec.ofNat 64 k) := by
        intro k hk
        rw [writeW_byte_off _ _ _ _ ?_, m₃, m₂]
        have hc : (VG.Proof.ChaCha20.X86.Quad.dW a W).Contains (a + BitVec.ofNat 64 k) 1 := Offset.contains_base a (by omega) (by lit_omega)
        by_contra hlt'
        rw [BitVec.add_zero] at hlt'
        exact hdb _ hc (by simp only [Region.Contains]; omega)
      refine ⟨fun k hk => ?_, fun hz _ i hi => ?_, fun l' hl' j hj hr' => ?_, ?_, ?_, ?_, ?_⟩
      · show (s₃.mem.writeW _ _) _ = _
        rw [hm k hk, h.data k hk]
        by_cases c : k % 64 / 16 = r ∧ k / 64 < l ∧ VG.Proof.ChaCha20.X86.Quad.Full W k
        · rw [ite_eq_left c, ite_eq_left ⟨c.1, by omega, c.2.2⟩]
        · rw [ite_eq_right c, ite_eq_right (by simp only [VG.Proof.ChaCha20.X86.Quad.Full, chunkOff] at *; omega)]
      · show (s₃.mem.writeW _ _) _ = _
        have hs : VG.Proof.ChaCha20.X86.Quad.sOff W = chunkOff r l := by simp only [VG.Proof.ChaCha20.X86.Quad.sOff, chunkOff] at *; omega
        rw [show buf + BitVec.ofNat 64 i = buf + BitVec.ofNat 64 0 + BitVec.ofNat 64 i by
            rw [Offset.add_add, Nat.zero_add], writeW_byte _ _ _ (by omega) (by lit_omega), hs, x₃, x₂]
        exact VG.Proof.ChaCha20.X86.Quad.reg_byte hr (fun j hj => hreg j hj hr) (by omega)
      · show dword (s₃.xmm (outReg l')) j = _
        rw [x₃, x₂]; exact h.regs l' hl' j hj hr'
      · show Frame _ _ (s₃.mem.writeW _ _)
        rw [m₃, m₂]
        exact h.frame.trans ((Frame.refl _ _).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
          (Offset.contains_base buf (by decide) (by decide)))
      · show s₃.gpr = _; rw [g₃, g₂, h.gpr]
      · show s₃.rd = _; rw [r₃, r₂, h.rd]
      · show s₃.wr = _; rw [w₃, w₂, h.wr]
  · -- All 16 bytes within the data: XORed.
    simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    have hfull : chunkOff r l + 16 ≤ W := by omega
    refine WP.mono (VG.Proof.ChaCha20.X86.Quad.xor16_ok (VG.Proof.ChaCha20.X86.Quad.outReg_ne6 l hl) hW256 hfull ((hd.of h.gpr h.wr).of g₂ w₂))
      fun s' ⟨hm, hf, hx, hg, hrd, hwr⟩ => ⟨fun k hk => ?_, fun hz hdn i hi => ?_,
        fun l' hl' j hj hr' => ?_, ?_, ?_, ?_, ?_⟩
    · rw [hm k hk, m₂, h.data k hk]
      by_cases hin : chunkOff r l ≤ k ∧ k < chunkOff r l + 16
      · have c₁ : ¬ (k % 64 / 16 = r ∧ k / 64 < l ∧ VG.Proof.ChaCha20.X86.Quad.Full W k) := by simp only [chunkOff] at hin; omega
        have c₂ : k % 64 / 16 = r ∧ k / 64 < l + 1 ∧ VG.Proof.ChaCha20.X86.Quad.Full W k := by simp only [VG.Proof.ChaCha20.X86.Quad.Full, chunkOff] at *; omega
        rw [ite_eq_left hin, ite_eq_right c₁, ite_eq_left c₂, x₂,
          show k = chunkOff r l + (k - chunkOff r l) by omega, Nat.add_sub_cancel_left,
          VG.Proof.ChaCha20.X86.Quad.reg_byte hr (fun j hj => hreg j hj hr) (by omega)]
        simp only [chunkOff]
      · rw [ite_eq_right hin]
        by_cases c : k % 64 / 16 = r ∧ k / 64 < l ∧ VG.Proof.ChaCha20.X86.Quad.Full W k
        · rw [ite_eq_left c, ite_eq_left ⟨c.1, by omega, c.2.2⟩]
        · rw [ite_eq_right c, ite_eq_right (by simp only [chunkOff] at hin; omega)]
    · rw [hf _ (VG.Proof.ChaCha20.X86.Quad.stash_out hdb (by omega)), m₂]
      exact h.stash hz (by simp only [VG.Proof.ChaCha20.X86.Quad.sOff, chunkOff] at *; omega) i hi
    · rw [hx _ (VG.Proof.ChaCha20.X86.Quad.outReg_ne6 l' hl'), x₂]; exact h.regs l' hl' j hj hr'
    · exact h.frame.trans ((m₂ ▸ hf).mono (by simp))
    · rw [hg, g₂, h.gpr]
    · rw [hrd, r₂, h.rd]
    · rw [hwr, w₂, h.wr]

end Chunk

/-! ## The whole output -/

/-- Block `l` of the four: the rounds' result `vs l` plus the input state `ctr C l`. -/
abbrev blk (vs : Nat → CState) (C : CState) (l : Nat) : CState :=
  Vector.zipWith (· + ·) (vs l) (ctr C l)

/-- After rows below `r`: those rows of the four blocks are XORed into the
data, but for the 16 bytes past its end, if any, which are in `buf[0, 16)`;
only the data and `buf[0, 16)` have been written since `s₀`. -/
structure FI (a buf : Addr) (B : Nat → CState) (W r : Nat) (s₀ s : State) : Prop where
  data : ∀ k, k < W → s.mem (a + BitVec.ofNat 64 k) =
    if k % 64 / 16 < r ∧ VG.Proof.ChaCha20.X86.Quad.Full W k then s₀.mem (a + BitVec.ofNat 64 k) ^^^ VG.Proof.ChaCha20.X86.Quad.ksb B k
    else s₀.mem (a + BitVec.ofNat 64 k)
  stash : VG.Proof.ChaCha20.X86.Quad.Stashed buf B W (fun o => o % 64 / 16 < r) s.mem
  frame : Frame [VG.Proof.ChaCha20.X86.Quad.dW a W, VG.Proof.ChaCha20.X86.Quad.stashR buf] s₀.mem s.mem
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem FI.zero (a buf : Addr) (B : Nat → CState) (W : Nat) (s₀ : State) : VG.Proof.ChaCha20.X86.Quad.FI a buf B W 0 s₀ s₀ :=
  ⟨fun k _ => by rw [ite_eq_right (by omega)], fun _ h => absurd h (Nat.not_lt_zero _),
    Frame.refl _ _, rfl, rfl, rfl⟩

section
variable {st buf a : Addr} {vs : Nat → CState} {C : CState} {W n : Nat} {s₀ : State}
  (hc : VG.Proof.ChaCha20.X86.Quad.Ctx st buf s₀) (hd : VG.Proof.ChaCha20.X86.Quad.DCtx a W s₀) (hn : n < 2 ^ 32) (hW : W = min n 256)
  (hebp : s₀.gpr .ebp = BitVec.ofNat 32 n) (db : (VG.Proof.ChaCha20.X86.Quad.dW a W).Disjoint (VG.Proof.ChaCha20.X86.Quad.bufR buf))
  (ds : (VG.Proof.ChaCha20.X86.Quad.dW a W).Disjoint (VG.Proof.ChaCha20.X86.Quad.stR st))
include hc hd hn hW hebp db ds

omit ds in
theorem finishRow_ok {r : Nat} (hr : r < 4) {s : State} (h : VG.Proof.ChaCha20.X86.Quad.FI a buf (VG.Proof.ChaCha20.X86.Quad.blk vs C) W r s₀ s)
    (hh : VG.Proof.ChaCha20.X86.Quad.RowHolds buf vs r s.mem) (hct : VG.Proof.ChaCha20.X86.Quad.Ctrs buf C 4 s.mem) (hC : stateAt s.mem st = C) :
    WP isa (finishRow r) s (VG.Proof.ChaCha20.X86.Quad.FI a buf (VG.Proof.ChaCha20.X86.Quad.blk vs C) W (r + 1) s₀) := by
  have hcs := hc.of h.gpr h.wr
  have hdb : (VG.Proof.ChaCha20.X86.Quad.dW a W).Disjoint (VG.Proof.ChaCha20.X86.Quad.stashR buf) := db.sub_right (Region.sub_prefix (by decide))
  rw [finishRow]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.ChaCha20.X86.Quad.loadRow_ok hr hcs hh) fun s₁ ⟨hreg, hrow, hm₁, hg₁, hrd₁, hwr₁⟩ => ?_
  rw [WP.block_append_iff]
  have aw₀ : VG.Proof.ChaCha20.X86.Quad.AW vs C r 0 s₁ s₁ :=
    ⟨fun j hj _ l hl => by rw [ite_eq_right (Nat.not_lt_zero _)]; exact hreg j hj l hl,
      by rw [hC] at hrow; exact hrow, rfl, rfl, rfl, rfl⟩
  refine WP.mono (wp_range_flatMap (M := isa) (fun i s => VG.Proof.ChaCha20.X86.Quad.AW vs C r i s₁ s)
    (fun i s hi hs => VG.Proof.ChaCha20.X86.Quad.addWord_ok hr hi (hcs.of hg₁ hwr₁) (hm₁ ▸ hct) hs) 4 (Nat.le_refl _) s₁ aw₀)
    fun s₂ h₂ => ?_
  refine WP.mono (VG.Proof.ChaCha20.X86.Quad.transpose_ok s₂) fun s₃ ⟨ht, hm₃, hg₃, hrd₃, hwr₃⟩ => ?_
  have hm : s₃.mem = s.mem := by rw [hm₃, h₂.mem, hm₁]
  have hg : s₃.gpr = s₀.gpr := by rw [hg₃, h₂.gpr, hg₁, h.gpr]
  have hw : s₃.wr = s₀.wr := by rw [hwr₃, h₂.wr, hwr₁, h.wr]
  have hd₃ : VG.Proof.ChaCha20.X86.Quad.DCtx a W s₃ := hd.of hg hw
  have hbe : s₃.ea (at_ .edi 0) = buf + BitVec.ofNat 64 0 := (VG.Proof.ChaCha20.X86.Quad.ea_gpr hg _).trans (hc.eaB 0 (by decide))
  have hebp₃ : s₃.gpr .ebp = BitVec.ofNat 32 n := by rw [hg, hebp]
  have hwb₃ : VG.Proof.ChaCha20.X86.Quad.bufR buf ∈ s₃.wr := hw ▸ hc.wb
  have xo₀ : VG.Proof.ChaCha20.X86.Quad.XO a buf (VG.Proof.ChaCha20.X86.Quad.blk vs C) W r 0 s₃ s₃ :=
    ⟨fun k _ => by rw [ite_eq_right (by omega)],
      fun hz hdn i hi => by rw [hm]; exact h.stash hz (by omega) i hi,
      fun l' hl' j hj hr' => by rw [ht l' hl' j hj, h₂.regs j hj hr' l' hl', ite_eq_left hj, Vector.getElem_zipWith],
      Frame.refl _ _, rfl, rfl, rfl⟩
  have step := fun l (hl : l < 4) {s : State} (hs : VG.Proof.ChaCha20.X86.Quad.XO a buf (VG.Proof.ChaCha20.X86.Quad.blk vs C) W r l s₃ s) =>
    VG.Proof.ChaCha20.X86.Quad.chunk_ok hn hW hd₃ hbe hwb₃ hdb hebp₃ hr hl hs
  refine WP.seq (WP.mono (step 0 (by decide) xo₀) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (step 1 (by decide) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (step 2 (by decide) h₅) fun s₆ h₆ => ?_)
  refine WP.mono (step 3 (by decide) h₆) fun s₇ h₇ => ⟨fun k hk => ?_, fun hz hdn i hi => ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₇.data k hk, hm, h.data k hk]
    by_cases c : k % 64 / 16 = r
    · by_cases cf : VG.Proof.ChaCha20.X86.Quad.Full W k
      · rw [ite_eq_left ⟨c, by omega, cf⟩, ite_eq_right (by omega), ite_eq_left ⟨by omega, cf⟩]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega)]
      by_cases c' : k % 64 / 16 < r ∧ VG.Proof.ChaCha20.X86.Quad.Full W k
      · rw [ite_eq_left c', ite_eq_left ⟨by omega, c'.2⟩]
      · rw [ite_eq_right c', ite_eq_right (by omega)]
  · exact h₇.stash hz (by simp only [VG.Proof.ChaCha20.X86.Quad.sOff] at *; omega) i hi
  · exact h.frame.trans (hm ▸ h₇.frame)
  · rw [h₇.gpr, hg]
  · rw [h₇.rd, hrd₃, h₂.rd, hrd₁, h.rd]
  · rw [h₇.wr, hw]

omit hd hn hW hebp in
/-- Rows `r ≥ 1` still find their words, the counters and the state, which
the output has not written. -/
theorem rowPre {r : Nat} (hr : r < 4) (hr1 : 1 ≤ r) (hh : VG.Proof.ChaCha20.X86.Quad.Holds4 buf vs s₀.mem) (hct : VG.Proof.ChaCha20.X86.Quad.Ctrs buf C 4 s₀.mem)
    (hC : stateAt s₀.mem st = C) {s : State} (h : VG.Proof.ChaCha20.X86.Quad.FI a buf (VG.Proof.ChaCha20.X86.Quad.blk vs C) W r s₀ s) :
    VG.Proof.ChaCha20.X86.Quad.RowHolds buf vs r s.mem ∧ VG.Proof.ChaCha20.X86.Quad.Ctrs buf C 4 s.mem ∧ stateAt s.mem st = C := by
  have hs : ∀ d, 16 ≤ d → d + 4 ≤ 320 → ∀ r' ∈ [VG.Proof.ChaCha20.X86.Quad.dW a W, VG.Proof.ChaCha20.X86.Quad.stashR buf],
      (⟨buf + BitVec.ofNat 64 d, 4⟩ : Region).Disjoint r' := by
    intro d h16 h320 r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact (db.sub_right (Offset.sub_base buf h320)).symm
    · exact Offset.disjoint_base buf h16 (by lit_omega)
  refine ⟨fun i hi _ l hl => ?_, fun l hl => ?_, ?_⟩
  · rw [h.frame.readW (Region.contains_self _ _) (hs _ (by omega) (by omega)) (by decide)]
    exact hh _ (by omega) l hl
  · rw [h.frame.readW (Region.contains_self _ _) (hs _ (by simp only [ctrOff]; omega)
      (by simp only [ctrOff]; omega)) (by decide)]
    exact hct l hl
  · rw [VG.Proof.ChaCha20.X86.Quad.stateAt_frame h.frame (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r' (rfl | rfl)
      · exact ds.symm
      · exact hc.sb.sub_right (Region.sub_prefix (by decide)))]
    exact hC

theorem finish4_ok (hh : VG.Proof.ChaCha20.X86.Quad.Holds4 buf vs s₀.mem) (hct : VG.Proof.ChaCha20.X86.Quad.Ctrs buf C 4 s₀.mem) (hC : stateAt s₀.mem st = C) :
    WP isa finish4 s₀ (VG.Proof.ChaCha20.X86.Quad.FI a buf (VG.Proof.ChaCha20.X86.Quad.blk vs C) W 4 s₀) := by
  have row := fun r (hr : r < 4) {s : State} (h : VG.Proof.ChaCha20.X86.Quad.FI a buf (VG.Proof.ChaCha20.X86.Quad.blk vs C) W r s₀ s)
      (p : VG.Proof.ChaCha20.X86.Quad.RowHolds buf vs r s.mem ∧ VG.Proof.ChaCha20.X86.Quad.Ctrs buf C 4 s.mem ∧ stateAt s.mem st = C) =>
    VG.Proof.ChaCha20.X86.Quad.finishRow_ok hc hd hn hW hebp db hr h p.1 p.2.1 p.2.2
  have pre := fun r (hr : r < 4) (hr1 : 1 ≤ r) {s : State} (h : VG.Proof.ChaCha20.X86.Quad.FI a buf (VG.Proof.ChaCha20.X86.Quad.blk vs C) W r s₀ s) =>
    VG.Proof.ChaCha20.X86.Quad.rowPre hc db ds hr hr1 hh hct hC h
  unfold finish4
  refine WP.seq (WP.mono (row 0 (by decide) (FI.zero a buf _ W s₀)
    ⟨fun i hi _ l hl => hh _ (by omega) l hl, hct, hC⟩) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (row 1 (by decide) h₁ (pre 1 (by decide) (by decide) h₁)) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (row 2 (by decide) h₂ (pre 2 (by decide) (by decide) h₂)) fun s₃ h₃ => ?_)
  exact row 3 (by decide) h₃ (pre 3 (by decide) (by decide) h₃)

end

end VG.Proof.ChaCha20.X86.Quad

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86.Kernels`. -/
section

/-!
# ChaCha20 on x86 (32-bit): the quarter rounds of the four-block code

`sse2Ok` and `ssse3Ok` are what the four-block code needs of its quarter
round (`Quad.KernelOk`): `vqr` needs nothing; `vqr3` needs its `pshufb`
controls in `buf[288, 320)`, which `masks` stores there and the four-block
code never writes.
-/

namespace VG.Proof.ChaCha20.X86.Kernels

open VG VG.X86 VG.Impl.ChaCha20.X86 VG.Impl.ChaCha20.X86.Xor
open VG.Proof.ChaCha20.X86.Quad (KernelOk kR bufR in_buf out_buf w32_other)

/-- `vqr`, in the baseline ISA. -/
def sse2Ok : VG.Proof.ChaCha20.X86.Quad.KernelOk sse2 where
  Inv _ _ := True
  inv_frame _ _ _ := trivial
  qr_ok hab hac had hbc hbd hcd ha hb hc hd s _ _ _ := VG.Proof.ChaCha20.X86.vqr_ok hab hac had hbc hbd hcd ha hb hc hd s
  init_ok _ _ _ := WP.block_nil ⟨trivial, Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩

/-- `vqr3`'s controls are in `buf`. -/
def Masks (buf : Addr) (m : Mem) : Prop :=
  m.readW (buf + BitVec.ofNat 64 rot16Off) 128 = VG.Proof.ChaCha20.X86.mask16 ∧ m.readW (buf + BitVec.ofNat 64 rot8Off) 128 = VG.Proof.ChaCha20.X86.mask8

theorem maskWords_getD : ∀ k, k < 8 → (maskWords.getD k (0, 0)).2 = 288 + 4 * k := by decide

theorem masks_eq : masks = (List.range 8).flatMap fun k =>
    [.mov .eax (.imm (maskWords.getD k (0, 0)).1), .store (at_ .edi (maskWords.getD k (0, 0)).2) .eax] := rfl

/-- After the stores of the first `n` words of the controls. -/
structure MI (buf : Addr) (s₀ : State) (n : Nat) (s : State) : Prop where
  words : ∀ k, k < n → s.mem.readW (buf + BitVec.ofNat 64 (288 + 4 * k)) 32 = (maskWords.getD k (0, 0)).1
  frame : Frame [VG.Proof.ChaCha20.X86.Quad.kR buf] s₀.mem s.mem
  keep : ∀ r, r ≠ .eax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem mask_dwords (buf : Addr) (m : Mem) {o : Nat} {v : BitVec 128}
    (h : ∀ i, i < 4 → m.readW (buf + BitVec.ofNat 64 (o + 4 * i)) 32 = dword v i) :
    m.readW (buf + BitVec.ofNat 64 o) 128 = v := by
  have e : ∀ i, i < 4 → dword (m.readW (buf + BitVec.ofNat 64 o) 128) i = dword v i := fun i hi => by
    rw [dword_readW _ _ hi, Offset.add_add]; exact h i hi
  exact ext_dword (e 0 (by decide)) (e 1 (by decide)) (e 2 (by decide)) (e 3 (by decide))

/-- `vqr3`, with SSSE3. -/
def ssse3Ok : VG.Proof.ChaCha20.X86.Quad.KernelOk ssse3 where
  Inv := VG.Proof.ChaCha20.X86.Kernels.Masks
  inv_frame {buf m m' rs} h hf hd :=
    ⟨by rw [hf.readW (r := VG.Proof.ChaCha20.X86.Quad.kR buf) (Offset.contains _ (by decide) (by decide) (by decide)) hd (by decide)]
        exact h.1,
     by rw [hf.readW (r := VG.Proof.ChaCha20.X86.Quad.kR buf) (Offset.contains _ (by decide) (by decide) (by decide)) hd (by decide)]
        exact h.2⟩
  qr_ok := fun {buf} {_ _ _ _} hab hac had hbc hbd hcd ha hb hc hd s he hw hi =>
    VG.Proof.ChaCha20.X86.vqr3_ok hab hac had hbc hbd hcd ha hb hc hd s (he _ (by decide)) (he _ (by decide))
      (VG.Proof.ChaCha20.X86.Quad.in_buf (d := rot16Off) hw (by decide)) (VG.Proof.ChaCha20.X86.Quad.in_buf (d := rot8Off) hw (by decide)) hi.1 hi.2
  init_ok {buf} s he hw := by
    show WP isa (.block masks) s _
    rw [VG.Proof.ChaCha20.X86.Kernels.masks_eq]
    refine WP.mono (wp_range_flatMap (M := isa) (VG.Proof.ChaCha20.X86.Kernels.MI buf s) (fun k s' hk h => ?_) 8 (Nat.le_refl _) s
      ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, fun _ _ => rfl, rfl, rfl⟩) fun s' h => ?_
    · have hd := VG.Proof.ChaCha20.X86.Kernels.maskWords_getD k hk
      have e : VG.X86.addr (s.gpr .edi) (maskWords.getD k (0, 0)).2 = buf + BitVec.ofNat 64 (288 + 4 * k) := by
        rw [hd]; exact he _ (by omega)
      refine Wp.wp_movi fun s₁ u₁ => ?_
      refine Wp.wp_stm (by rw [u₁.other _ (by decide), h.keep _ (by decide)])
        (by rw [e, u₁.wr, h.wr]; exact VG.Proof.ChaCha20.X86.Quad.out_buf hw (by omega)) fun s₂ u₂ => WP.block_nil ?_
      have hm : s₂.mem = s'.mem.writeW (buf + BitVec.ofNat 64 (288 + 4 * k)) (maskWords.getD k (0, 0)).1 := by
        rw [u₂.mem, e, u₁.gpr, u₁.mem]
      refine ⟨fun j hj => ?_, ?_, fun r hr => ?_, by rw [u₂.rd, u₁.rd, h.rd], by rw [u₂.wr, u₁.wr, h.wr]⟩
      · rw [hm]
        by_cases hjk : j = k
        · subst hjk; exact Mem.readW_writeW_self32 _ _ _
        · rw [VG.Proof.ChaCha20.X86.Quad.w32_other _ _ _ (by omega) (by omega) (by omega)]; exact h.words j (by omega)
      · rw [hm]
        exact h.frame.writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by decide))
      · rw [u₂.gpr, u₁.other r hr, h.keep r hr]
    · refine ⟨⟨VG.Proof.ChaCha20.X86.Kernels.mask_dwords buf s'.mem (o := 288) fun i hi => ?_,
        VG.Proof.ChaCha20.X86.Kernels.mask_dwords buf s'.mem (o := 304) fun i hi => ?_⟩, h.frame, h.keep, h.rd, h.wr⟩
      · rw [h.words i (by omega)]
        rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
      · rw [show 304 + 4 * i = 288 + 4 * (i + 4) by omega, h.words (i + 4) (by omega)]
        rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl

end VG.Proof.ChaCha20.X86.Kernels

end

/- Proofs formerly in `VerifiedGarbage.Proof.ChaCha20.X86.Xor`. -/
section

/-!
# ChaCha20 keystream XOR on x86 (32-bit)

The invariant before each group of four blocks (`OInv`) holds before the
loop over four blocks (`body4_ok`, with the setup, rounds and output of
`Quad.lean`), which ends with the data done or at most 64 bytes left; those
are the block function's output XORed into the data (`tail_ok`). The call
runs in a frame holding its two arguments (`WP.frame`), and the block
function's own `Verified` proof gives its effect (`WP.call`); the frame and
the return address are in the 12 bytes of stack below `esp` that the
contract reserves.

Constant time is the taint analysis's, which follows the frames and the
calls into the block function. `xor_eax` states that `eax` holds `buf` on
return.
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.X86

/-- X86 (32-bit) contract for `vg_chacha20_xor(state: *mut [u32; 16], data: *mut
u8, len: usize, buf: *mut [u32; 80])`, whose arguments are on the stack (cdecl):
XORs the first `len` bytes of the keystream of the state at `state` into the
`len` bytes at `data`.

The code may read and write the arguments (16 bytes above the return
address), `state` (64 bytes; its contents on exit are unspecified), `data`
(`len` bytes) and `buf` (320 bytes of working space). These may not overlap
each other; the buffers may not overlap the return address or the 12 bytes
of stack below it, where the calls of the block function store their
arguments and return address; nothing may wrap around the end of the
(32-bit) address space. `esp` and the arguments (the pointers and the length)
are public; the state and the data are secret. -/
def xorX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let data : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let buf : Region := ⟨(arg s 3).setWidth 64, 320⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
    s.rd = [] ∧ s.wr = [state, data, buf, args] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    args.Disjoint state ∧ args.Disjoint data ∧ args.Disjoint buf ∧
    ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint buf ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint buf ∧
    (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 320 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    bytesAt s'.mem ((arg s 1).setWidth 64) (arg s 2).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
        (keystream (stateAt s.mem ((arg s 0).setWidth 64)) (arg s 2).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86.Xor

open VG VG.X86 VG.Impl.ChaCha20.X86.Xor
open VG.Impl.ChaCha20.X86 (at_)
open VG.Proof.ChaCha20.X86 (contains_off contains_sub toNat_ofNat_lt readW_writeW_off block_correct)
open VG.Proof.ChaCha20.X86.Bytes (toNat_ofNat_lt32 ptr_add BPre BPost WPre xorBytes_ok xorWide_ok and_m16
  and_15 setWidth_add ofNat32_add_toNat)
open VG.Spec.ChaCha20 (stateAt keystream serialize bytesAt)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev E : BitVec 32 := s₀.gpr .esp
abbrev ST : BitVec 32 := arg s₀ 0
abbrev DP : BitVec 32 := arg s₀ 1
abbrev LN : BitVec 32 := arg s₀ 2
abbrev BP : BitVec 32 := arg s₀ 3
abbrev L : Nat := (VG.Proof.ChaCha20.X86.Xor.LN s₀).toNat
abbrev st : Addr := (VG.Proof.ChaCha20.X86.Xor.ST s₀).setWidth 64
abbrev dp : Addr := (VG.Proof.ChaCha20.X86.Xor.DP s₀).setWidth 64
abbrev bp : Addr := (VG.Proof.ChaCha20.X86.Xor.BP s₀).setWidth 64
abbrev stR : Region := ⟨VG.Proof.ChaCha20.X86.Xor.st s₀, 64⟩
abbrev dR : Region := ⟨VG.Proof.ChaCha20.X86.Xor.dp s₀, VG.Proof.ChaCha20.X86.Xor.L s₀⟩
abbrev bR : Region := ⟨VG.Proof.ChaCha20.X86.Xor.bp s₀, 320⟩
abbrev aR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(VG.Proof.ChaCha20.X86.Xor.E s₀).setWidth 64, 4⟩
abbrev stackR : Region := ⟨(VG.Proof.ChaCha20.X86.Xor.E s₀).setWidth 64 - 12, 12⟩
/-- The state, the data and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (VG.Proof.ChaCha20.X86.Xor.st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (VG.Proof.ChaCha20.X86.Xor.S0 s₀) (VG.Proof.ChaCha20.X86.Xor.L s₀)
/-- The bytes of data done before block `j`. -/
abbrev P (j : Nat) : Nat := min (64 * j) (VG.Proof.ChaCha20.X86.Xor.L s₀)
/-- How many bytes of block `j` are used. -/
abbrev C (j : Nat) : Nat := min 64 (VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ j)
end

theorem L_lt (s₀ : State) : VG.Proof.ChaCha20.X86.Xor.L s₀ < 2 ^ 32 := (VG.Proof.ChaCha20.X86.Xor.LN s₀).isLt

structure XPre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [VG.Proof.ChaCha20.X86.Xor.stR s₀, VG.Proof.ChaCha20.X86.Xor.dR s₀, VG.Proof.ChaCha20.X86.Xor.bR s₀, VG.Proof.ChaCha20.X86.Xor.aR s₀]
  st_d : (VG.Proof.ChaCha20.X86.Xor.stR s₀).Disjoint (VG.Proof.ChaCha20.X86.Xor.dR s₀)
  st_b : (VG.Proof.ChaCha20.X86.Xor.stR s₀).Disjoint (VG.Proof.ChaCha20.X86.Xor.bR s₀)
  d_b : (VG.Proof.ChaCha20.X86.Xor.dR s₀).Disjoint (VG.Proof.ChaCha20.X86.Xor.bR s₀)
  a_st : (VG.Proof.ChaCha20.X86.Xor.aR s₀).Disjoint (VG.Proof.ChaCha20.X86.Xor.stR s₀)
  a_d : (VG.Proof.ChaCha20.X86.Xor.aR s₀).Disjoint (VG.Proof.ChaCha20.X86.Xor.dR s₀)
  a_b : (VG.Proof.ChaCha20.X86.Xor.aR s₀).Disjoint (VG.Proof.ChaCha20.X86.Xor.bR s₀)
  ret_st : (VG.Proof.ChaCha20.X86.Xor.retR s₀).Disjoint (VG.Proof.ChaCha20.X86.Xor.stR s₀)
  ret_d : (VG.Proof.ChaCha20.X86.Xor.retR s₀).Disjoint (VG.Proof.ChaCha20.X86.Xor.dR s₀)
  ret_b : (VG.Proof.ChaCha20.X86.Xor.retR s₀).Disjoint (VG.Proof.ChaCha20.X86.Xor.bR s₀)
  stk_st : (VG.Proof.ChaCha20.X86.Xor.stackR s₀).Disjoint (VG.Proof.ChaCha20.X86.Xor.stR s₀)
  stk_d : (VG.Proof.ChaCha20.X86.Xor.stackR s₀).Disjoint (VG.Proof.ChaCha20.X86.Xor.dR s₀)
  stk_b : (VG.Proof.ChaCha20.X86.Xor.stackR s₀).Disjoint (VG.Proof.ChaCha20.X86.Xor.bR s₀)
  st_fit : (VG.Proof.ChaCha20.X86.Xor.ST s₀).toNat + 64 ≤ 2 ^ 32
  d_fit : (VG.Proof.ChaCha20.X86.Xor.DP s₀).toNat + VG.Proof.ChaCha20.X86.Xor.L s₀ ≤ 2 ^ 32
  b_fit : (VG.Proof.ChaCha20.X86.Xor.BP s₀).toNat + 320 ≤ 2 ^ 32
  sp_lo : 12 ≤ (VG.Proof.ChaCha20.X86.Xor.E s₀).toNat
  sp_hi : (VG.Proof.ChaCha20.X86.Xor.E s₀).toNat + 20 ≤ 2 ^ 32

theorem XPre.of (s₀ : State) (h : Proof.ChaCha20.xorX86.pre s₀) : VG.Proof.ChaCha20.X86.Xor.XPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩

/-- Our caller's `ebx, esi, edi, ebp`, saved in `buf[256, 272)`. -/
abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (VG.Proof.ChaCha20.X86.Xor.bp s₀ + BitVec.ofNat 64 ·) s₀.gpr saved

theorem saved_fits : Spill.Fits 272 saved := by decide

/-- The regions the code writes: its buffers and the 12 bytes of stack of its calls. -/
abbrev frameR (s₀ : State) : List Region := [VG.Proof.ChaCha20.X86.Xor.stR s₀, VG.Proof.ChaCha20.X86.Xor.dR s₀, VG.Proof.ChaCha20.X86.Xor.bR s₀, VG.Proof.ChaCha20.X86.Xor.stackR s₀]

/-- Before block `j` (the loop's invariant); the counter (word 12 of the
state) is block `j`'s while there are bytes left. -/
structure OInv (s₀ : State) (j : Nat) (s : State) : Prop where
  ebx : s.gpr .ebx = VG.Proof.ChaCha20.X86.Xor.ST s₀
  esi : s.gpr .esi = VG.Proof.ChaCha20.X86.Xor.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Xor.P s₀ j)
  edi : s.gpr .edi = VG.Proof.ChaCha20.X86.Xor.BP s₀
  ebp : s.gpr .ebp = BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ j)
  esp : s.gpr .esp = VG.Proof.ChaCha20.X86.Xor.E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : VG.Proof.ChaCha20.X86.Xor.P s₀ j < VG.Proof.ChaCha20.X86.Xor.L s₀ → stateAt s.mem (VG.Proof.ChaCha20.X86.Xor.st s₀) = ctr (VG.Proof.ChaCha20.X86.Xor.S0 s₀) j
  data : ∀ k < VG.Proof.ChaCha20.X86.Xor.L s₀, s.mem (VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 k) =
    if k < VG.Proof.ChaCha20.X86.Xor.P s₀ j then VG.Proof.ChaCha20.X86.Xor.D0 s₀ k ^^^ (VG.Proof.ChaCha20.X86.Xor.KS s₀).getD k 0 else VG.Proof.ChaCha20.X86.Xor.D0 s₀ k
  saved : VG.Proof.ChaCha20.X86.Xor.Saved s₀ s.mem
  frame : Frame (VG.Proof.ChaCha20.X86.Xor.frameR s₀) s₀.mem s.mem

/-! ## Memory -/

namespace XPre
variable {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀)
include hp

theorem w_b : VG.Proof.ChaCha20.X86.Xor.bR s₀ ∈ s₀.wr := by simp [hp.wr]

theorem eaS {d : Nat} (hd : d < 64) : addr (VG.Proof.ChaCha20.X86.Xor.ST s₀) d = VG.Proof.ChaCha20.X86.Xor.st s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.st_fit; omega)

theorem eaB {d : Nat} (hd : d < 320) : addr (VG.Proof.ChaCha20.X86.Xor.BP s₀) d = VG.Proof.ChaCha20.X86.Xor.bp s₀ + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.b_fit; omega)

theorem eaE {d : Nat} (hd : d < 20) : addr (VG.Proof.ChaCha20.X86.Xor.E s₀) d = (VG.Proof.ChaCha20.X86.Xor.E s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.sp_hi; omega)

theorem out_b {d n : Nat} (h : d + n ≤ 320) : InRegions s₀.wr (VG.Proof.ChaCha20.X86.Xor.bp s₀ + BitVec.ofNat 64 d) n :=
  ⟨VG.Proof.ChaCha20.X86.Xor.bR s₀, hp.w_b, VG.Proof.ChaCha20.X86.contains_off h (by lit_omega)⟩

theorem arg_contains {i : Nat} (hi : i < 4) : (VG.Proof.ChaCha20.X86.Xor.aR s₀).Contains (argAddr s₀ i) 4 := by
  simp only [VG.Proof.ChaCha20.X86.Xor.aR]
  rw [show argAddr s₀ i = addr (VG.Proof.ChaCha20.X86.Xor.E s₀) (4 + 4 * i) from rfl, hp.eaE (by lit_omega),
    show argAddr s₀ 0 = addr (VG.Proof.ChaCha20.X86.Xor.E s₀) 4 from rfl, hp.eaE (by lit_omega)]
  exact VG.Proof.ChaCha20.X86.contains_sub _ (by lit_omega) (by lit_omega) (by lit_omega)

theorem in_arg {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨VG.Proof.ChaCha20.X86.Xor.aR s₀, by simp [hp.wr], hp.arg_contains hi⟩

end XPre

theorem contains_ofNat {b : Addr} {len d n : Nat} (h : d + n ≤ len) (hd : d < 2 ^ 64) :
    (⟨b, len⟩ : Region).Contains (b + BitVec.ofNat 64 d) n := VG.Proof.ChaCha20.X86.contains_off h hd

/-- A state in memory outside a frame is unchanged. -/
theorem stateAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 64⟩ : Region).Disjoint r) : stateAt m' p = stateAt m p := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn]
  exact hf.readW (VG.Proof.ChaCha20.X86.Xor.contains_ofNat (by lit_omega) (by lit_omega)) hd (by decide)

/-- `buf[256, 272)`, where our caller's registers are saved. -/
abbrev savR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.X86.Xor.bp s₀ + BitVec.ofNat 64 256, 16⟩

theorem savR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86.Xor.savR s₀) (VG.Proof.ChaCha20.X86.Xor.bR s₀) := Offset.sub_base _ (by lit_omega)

/-- The saved registers survive a frame that does not touch them. -/
theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : VG.Proof.ChaCha20.X86.Xor.Saved s₀ m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (VG.Proof.ChaCha20.X86.Xor.savR s₀).Disjoint r) : VG.Proof.ChaCha20.X86.Xor.Saved s₀ m' :=
  Spill.Saved.of_frame h hf (fun p hp => by
    have := saved_fits.1 p hp
    have : 256 ≤ p.2 := by revert p hp; decide
    exact Offset.contains _ this (by lit_omega) (by lit_omega)) hd

/-! ## The prologue -/

theorem load_buf_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) :
    WP isa (.block [.mov .eax (.mem (at_ .esp 16))]) s₀ fun s => s = s₀.setReg .eax (VG.Proof.ChaCha20.X86.Xor.BP s₀) := by
  have i₃ : InRegions (s₀.rd ++ s₀.wr) ((s₀.gpr .esp + BitVec.ofNat 32 16).setWidth 64) 4 :=
    hp.in_arg (i := 3) (by lit_omega)
  have v₃ : s₀.mem.readW ((s₀.gpr .esp + BitVec.ofNat 32 16).setWidth 64) 32 = VG.Proof.ChaCha20.X86.Xor.BP s₀ := rfl
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea, at_, State.load32,
    i₃, v₃, ite_true, Option.map_some, Option.some.injEq, exists_eq_left']

/-- The memory after the prologue's stores. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (VG.Proof.ChaCha20.X86.Xor.bp s₀ + BitVec.ofNat 64 ·) s₀.gpr saved

theorem saveMem_frame {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) : Frame [VG.Proof.ChaCha20.X86.Xor.bR s₀] s₀.mem (VG.Proof.ChaCha20.X86.Xor.saveMem s₀) :=
  have _ := hp
  Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
    have := saved_fits.1 p h; VG.Proof.ChaCha20.X86.contains_off (by lit_omega) (by lit_omega)

theorem saveMem_saved (s₀ : State) : VG.Proof.ChaCha20.X86.Xor.Saved s₀ (VG.Proof.ChaCha20.X86.Xor.saveMem s₀) :=
  Spill.saveMem_saved_ofNat _ _ _ VG.Proof.ChaCha20.X86.Xor.saved_fits (by decide)

theorem saveMem_arg {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {i : Nat} (hi : i < 4) :
    (VG.Proof.ChaCha20.X86.Xor.saveMem s₀).readW (argAddr s₀ i) 32 = arg s₀ i :=
  (VG.Proof.ChaCha20.X86.Xor.saveMem_frame hp).readW (hp.arg_contains hi) (by simpa using hp.a_b) (by decide)

theorem save_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) :
    WP isa (.block save) (s₀.setReg .eax (VG.Proof.ChaCha20.X86.Xor.BP s₀)) fun s₁ =>
      s₁.gpr = (s₀.setReg .eax (VG.Proof.ChaCha20.X86.Xor.BP s₀)).gpr ∧ s₁.mem = VG.Proof.ChaCha20.X86.Xor.saveMem s₀ ∧ s₁.rd = s₀.rd ∧
        s₁.wr = s₀.wr := by
  have e : ∀ p ∈ saved, addr (VG.Proof.ChaCha20.X86.Xor.BP s₀) p.2 = VG.Proof.ChaCha20.X86.Xor.bp s₀ + BitVec.ofNat 64 p.2 :=
    fun p h => hp.eaB (by have := saved_fits.1 p h; lit_omega)
  have geax : (s₀.setReg .eax (VG.Proof.ChaCha20.X86.Xor.BP s₀)).gpr .eax = VG.Proof.ChaCha20.X86.Xor.BP s₀ := RegUpd.gpr_setReg_self _ _ _
  rw [show save = Spill.saveCode .eax saved ++ [] from rfl]
  refine Spill.save_ok saved (fun p h => by
      rw [geax, e p h]; exact hp.out_b (by have := saved_fits.1 p h; lit_omega))
    fun s₁ u => WP.block_nil ⟨u.gpr, ?_, u.rd, u.wr⟩
  rw [u.mem, geax]
  exact Spill.saveMem_congr _ _ e fun p h => RegUpd.gpr_setReg_of_ne _ _ (by revert p h; decide)

set_option simprocs false in
theorem load_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {s₁ : State}
    (hg : s₁.gpr = (s₀.setReg .eax (VG.Proof.ChaCha20.X86.Xor.BP s₀)).gpr) (hm : s₁.mem = VG.Proof.ChaCha20.X86.Xor.saveMem s₀) (hr : s₁.rd = s₀.rd)
    (hw : s₁.wr = s₀.wr) :
    WP isa (.block [.mov .edi (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
      .mov .esi (.mem (at_ .esp 8)), .mov .ebp (.mem (at_ .esp 12))]) s₁ (VG.Proof.ChaCha20.X86.Xor.OInv s₀ 0) := by
  have i₀ : InRegions (s₁.rd ++ s₁.wr) ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 4 :=
    hr ▸ hw ▸ hp.in_arg (i := 0) (by lit_omega)
  have i₁ : InRegions (s₁.rd ++ s₁.wr) ((s₀.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 4 :=
    hr ▸ hw ▸ hp.in_arg (i := 1) (by lit_omega)
  have i₂ : InRegions (s₁.rd ++ s₁.wr) ((s₀.gpr .esp + BitVec.ofNat 32 12).setWidth 64) 4 :=
    hr ▸ hw ▸ hp.in_arg (i := 2) (by lit_omega)
  have v₀ : (VG.Proof.ChaCha20.X86.Xor.saveMem s₀).readW ((s₀.gpr .esp + BitVec.ofNat 32 4).setWidth 64) 32 = VG.Proof.ChaCha20.X86.Xor.ST s₀ :=
    VG.Proof.ChaCha20.X86.Xor.saveMem_arg hp (i := 0) (by lit_omega)
  have v₁ : (VG.Proof.ChaCha20.X86.Xor.saveMem s₀).readW ((s₀.gpr .esp + BitVec.ofNat 32 8).setWidth 64) 32 = VG.Proof.ChaCha20.X86.Xor.DP s₀ :=
    VG.Proof.ChaCha20.X86.Xor.saveMem_arg hp (i := 1) (by lit_omega)
  have v₂ : (VG.Proof.ChaCha20.X86.Xor.saveMem s₀).readW ((s₀.gpr .esp + BitVec.ofNat 32 12).setWidth 64) 32 = VG.Proof.ChaCha20.X86.Xor.LN s₀ :=
    VG.Proof.ChaCha20.X86.Xor.saveMem_arg hp (i := 2) (by lit_omega)
  have gesp : s₁.gpr .esp = s₀.gpr .esp := by rw [hg]; rfl
  have geax : s₁.gpr .eax = VG.Proof.ChaCha20.X86.Xor.BP s₀ := by rw [hg]; rfl
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.ea, at_, State.load32, State.setReg, gesp, geax, hm,
    i₀, i₁, i₂, v₀, v₁, v₂, ite_true, ite_false, Option.map_some,
    Option.some.injEq, exists_eq_left']
  have hf := VG.Proof.ChaCha20.X86.Xor.saveMem_frame hp
  refine ⟨by simp (config := {decide := true}), by simp (config := {decide := true}) [VG.Proof.ChaCha20.X86.Xor.P],
    by simp (config := {decide := true}), by simp (config := {decide := true}) [VG.Proof.ChaCha20.X86.Xor.P],
    by simp (config := {decide := true}) [hg, State.setReg], hr, hw, ?_, fun k hk => ?_,
    VG.Proof.ChaCha20.X86.Xor.saveMem_saved s₀, hf.mono (by simp)⟩
  · intro _; rw [VG.Proof.ChaCha20.X86.Xor.stateAt_frame hf (by simpa using hp.st_b), ctr_zero]
  · simp only [VG.Proof.ChaCha20.X86.Xor.P, Nat.mul_zero, Nat.zero_min, Nat.not_lt_zero, ite_false]
    exact hf.bytes (R := VG.Proof.ChaCha20.X86.Xor.dR s₀) (by simpa using hp.d_b) (show VG.Proof.ChaCha20.X86.Xor.L s₀ ≤ 2 ^ 64 by have := VG.Proof.ChaCha20.X86.Xor.L_lt s₀; omega) hk

theorem prologue_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) :
    WP isa (.block prologue) (s₀.setReg .eax (VG.Proof.ChaCha20.X86.Xor.BP s₀)) (VG.Proof.ChaCha20.X86.Xor.OInv s₀ 0) := by
  rw [show prologue = save ++ [.mov .edi (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
      .mov .esi (.mem (at_ .esp 8)), .mov .ebp (.mem (at_ .esp 12))]
    from rfl, WP.block_append_iff]
  exact WP.mono (VG.Proof.ChaCha20.X86.Xor.save_ok hp) fun s₁ ⟨hg, hm, hr, hw⟩ => VG.Proof.ChaCha20.X86.Xor.load_ok hp hg hm hr hw

/-! ## Calling the block function -/

/-- `esp` as a 64-bit address. -/
abbrev Es (s₀ : State) : Addr := (VG.Proof.ChaCha20.X86.Xor.E s₀).setWidth 64

theorem setWidth_sub {x : BitVec 32} {d : Nat} (h : d ≤ x.toNat) :
    (x - BitVec.ofNat 32 d).setWidth 64 = x.setWidth 64 - BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := d) (by lit_omega), Nat.mod_eq_of_lt (a := x.toNat) (by lit_omega),
    Nat.mod_eq_of_lt (a := d) (by lit_omega)]
  omega

/-- The 8 bytes of the frame holding the block function's arguments. -/
abbrev fR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.X86.Xor.Es s₀ - 8, 8⟩
/-- The block function's return address. -/
abbrev cR (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.X86.Xor.Es s₀ - 12, 4⟩
/-- The first 256 bytes of `buf`, which the block function may write. -/
abbrev b256 (s₀ : State) : Region := ⟨VG.Proof.ChaCha20.X86.Xor.bp s₀, 256⟩

theorem fR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86.Xor.fR s₀) (VG.Proof.ChaCha20.X86.Xor.stackR s₀) := Offset.sub_below _ (by decide) (by decide)

theorem cR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86.Xor.cR s₀) (VG.Proof.ChaCha20.X86.Xor.stackR s₀) := Offset.sub_below _ (by decide) (by decide)

theorem b256_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86.Xor.b256 s₀) (VG.Proof.ChaCha20.X86.Xor.bR s₀) := Region.sub_prefix (by lit_omega)

theorem savR_b256 (s₀ : State) : (VG.Proof.ChaCha20.X86.Xor.savR s₀).Disjoint (VG.Proof.ChaCha20.X86.Xor.b256 s₀) := Offset.disjoint_base _ (by lit_omega) (by lit_omega)

/-- The permissions the block function is called with. -/
abbrev rdC (s₀ : State) : List Region := [VG.Proof.ChaCha20.X86.Xor.stR s₀, VG.Proof.ChaCha20.X86.Xor.fR s₀]
abbrev wrC (s₀ : State) : List Region := [VG.Proof.ChaCha20.X86.Xor.b256 s₀]

/-- The state the block function is entered in, from `s`. -/
abbrev entry (s : State) : State := (pushed [.edi, .ebx] s).callEntry

theorem entry_esp (s : State) :
    (VG.Proof.ChaCha20.X86.Xor.entry s).gpr .esp = s.gpr .esp - BitVec.ofNat 32 8 - 4 := by
  simp only [VG.Proof.ChaCha20.X86.Xor.entry, State.callEntry_esp, pushed_esp]; rfl

theorem entry_mem (s : State) :
    (VG.Proof.ChaCha20.X86.Xor.entry s).mem = ((s.mem.writeW ((s.gpr .esp - 4).setWidth 64) (s.gpr .edi)).writeW
      ((s.gpr .esp - 4 - 4).setWidth 64) (s.gpr .ebx)).writeW
      ((s.gpr .esp - BitVec.ofNat 32 8 - 4).setWidth 64) (s.unknowns 0) := by
  simp only [VG.Proof.ChaCha20.X86.Xor.entry, State.callEntry_mem, pushed_esp]
  simp [pushed, pushRegs, State.setReg]

/-- The words at `esp - 4`, `esp - 8` and `esp - 12` lie in the 12 bytes below `esp`. -/
theorem stack_contains (e : Addr) :
    (⟨e - 12, 12⟩ : Region).Contains (e - 4) (32 / 8) ∧ (⟨e - 12, 12⟩ : Region).Contains (e - 8) (32 / 8) ∧
      (⟨e - 12, 12⟩ : Region).Contains (e - 12) (32 / 8) :=
  ⟨Offset.contains_below e (by decide) (by decide) (by decide),
    Offset.contains_below e (by decide) (by decide) (by decide),
    Offset.contains_below e (by decide) (by decide) (by decide)⟩

/-- The words at `esp - 4`, `esp - 8` and `esp - 12` do not overlap. -/
theorem stack_seps (e : Addr) :
    Mem.Sep (e - 8) (32 / 8) (e - 12) (32 / 8) ∧ Mem.Sep (e - 4) (32 / 8) (e - 12) (32 / 8) ∧
      Mem.Sep (e - 4) (32 / 8) (e - 8) (32 / 8) :=
  ⟨Offset.sep_below e 12 (by decide) (by decide) (by decide) (by decide) (by decide),
    Offset.sep_below e 12 (by decide) (by decide) (by decide) (by decide) (by decide),
    Offset.sep_below e 12 (by decide) (by decide) (by decide) (by decide) (by decide)⟩

section
variable {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {s : State} (hE : s.gpr .esp = VG.Proof.ChaCha20.X86.Xor.E s₀)
include hp hE

theorem entry_addrs :
    ((s.gpr .esp - 4).setWidth 64 = VG.Proof.ChaCha20.X86.Xor.Es s₀ - 4) ∧ ((s.gpr .esp - 4 - 4).setWidth 64 = VG.Proof.ChaCha20.X86.Xor.Es s₀ - 8) ∧
    ((s.gpr .esp - BitVec.ofNat 32 8 - 4).setWidth 64 = VG.Proof.ChaCha20.X86.Xor.Es s₀ - 12) := by
  have hlo := hp.sp_lo
  rw [hE]
  refine ⟨VG.Proof.ChaCha20.X86.Xor.setWidth_sub (d := 4) (by lit_omega), ?_, ?_⟩
  · rw [show VG.Proof.ChaCha20.X86.Xor.E s₀ - 4 - 4 = VG.Proof.ChaCha20.X86.Xor.E s₀ - BitVec.ofNat 32 8 by rw [BitVec.sub_sub]; rfl, VG.Proof.ChaCha20.X86.Xor.setWidth_sub (by lit_omega)]; rfl
  · rw [show VG.Proof.ChaCha20.X86.Xor.E s₀ - BitVec.ofNat 32 8 - 4 = VG.Proof.ChaCha20.X86.Xor.E s₀ - BitVec.ofNat 32 12 by rw [BitVec.sub_sub]; rfl,
      VG.Proof.ChaCha20.X86.Xor.setWidth_sub (by lit_omega)]; rfl

theorem entry_frame : Frame [VG.Proof.ChaCha20.X86.Xor.stackR s₀] s.mem (VG.Proof.ChaCha20.X86.Xor.entry s).mem := by
  obtain ⟨a₁, a₂, a₃⟩ := VG.Proof.ChaCha20.X86.Xor.entry_addrs hp hE
  obtain ⟨c4, c8, c12⟩ := VG.Proof.ChaCha20.X86.Xor.stack_contains (VG.Proof.ChaCha20.X86.Xor.Es s₀)
  rw [VG.Proof.ChaCha20.X86.Xor.entry_mem, a₁, a₂, a₃]
  exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c4).writeW
    (List.mem_singleton_self _) _ c8).writeW (List.mem_singleton_self _) _ c12

theorem entry_argAddr0 : argAddr (VG.Proof.ChaCha20.X86.Xor.entry s) 0 = VG.Proof.ChaCha20.X86.Xor.Es s₀ - 8 := by
  have hlo := hp.sp_lo
  simp only [argAddr, VG.Proof.ChaCha20.X86.Xor.entry_esp, hE]
  rw [show VG.Proof.ChaCha20.X86.Xor.E s₀ - BitVec.ofNat 32 8 - 4 + BitVec.ofNat 32 (4 + 4 * 0) = VG.Proof.ChaCha20.X86.Xor.E s₀ - BitVec.ofNat 32 8 by
    rw [BitVec.sub_sub, Offset.sub_ofNat_eq (VG.Proof.ChaCha20.X86.Xor.E s₀) (show 8 ≤ 12 by decide)]; rfl, VG.Proof.ChaCha20.X86.Xor.setWidth_sub (by lit_omega)]; rfl

theorem entry_argAddr1 : argAddr (VG.Proof.ChaCha20.X86.Xor.entry s) 1 = VG.Proof.ChaCha20.X86.Xor.Es s₀ - 4 := by
  have hlo := hp.sp_lo
  simp only [argAddr, VG.Proof.ChaCha20.X86.Xor.entry_esp, hE]
  rw [show VG.Proof.ChaCha20.X86.Xor.E s₀ - BitVec.ofNat 32 8 - 4 + BitVec.ofNat 32 (4 + 4 * 1) = VG.Proof.ChaCha20.X86.Xor.E s₀ - BitVec.ofNat 32 4 by
    rw [BitVec.sub_sub, Offset.sub_ofNat_eq (VG.Proof.ChaCha20.X86.Xor.E s₀) (show 4 ≤ 12 by decide)]; rfl, VG.Proof.ChaCha20.X86.Xor.setWidth_sub (by lit_omega)]; rfl

theorem entry_arg0 (hb : s.gpr .ebx = VG.Proof.ChaCha20.X86.Xor.ST s₀) : arg (VG.Proof.ChaCha20.X86.Xor.entry s) 0 = VG.Proof.ChaCha20.X86.Xor.ST s₀ := by
  obtain ⟨a₁, a₂, a₃⟩ := VG.Proof.ChaCha20.X86.Xor.entry_addrs hp hE
  show (VG.Proof.ChaCha20.X86.Xor.entry s).mem.readW (argAddr (VG.Proof.ChaCha20.X86.Xor.entry s) 0) 32 = VG.Proof.ChaCha20.X86.Xor.ST s₀
  rw [VG.Proof.ChaCha20.X86.Xor.entry_argAddr0 hp hE, VG.Proof.ChaCha20.X86.Xor.entry_mem, a₁, a₂, a₃,
    Mem.readW_writeW_sep (VG.Proof.ChaCha20.X86.Xor.stack_seps _).1 (by decide), Mem.readW_writeW_self32, hb]

theorem entry_arg1 (hd : s.gpr .edi = VG.Proof.ChaCha20.X86.Xor.BP s₀) : arg (VG.Proof.ChaCha20.X86.Xor.entry s) 1 = VG.Proof.ChaCha20.X86.Xor.BP s₀ := by
  obtain ⟨a₁, a₂, a₃⟩ := VG.Proof.ChaCha20.X86.Xor.entry_addrs hp hE
  show (VG.Proof.ChaCha20.X86.Xor.entry s).mem.readW (argAddr (VG.Proof.ChaCha20.X86.Xor.entry s) 1) 32 = VG.Proof.ChaCha20.X86.Xor.BP s₀
  rw [VG.Proof.ChaCha20.X86.Xor.entry_argAddr1 hp hE, VG.Proof.ChaCha20.X86.Xor.entry_mem, a₁, a₂, a₃,
    Mem.readW_writeW_sep (VG.Proof.ChaCha20.X86.Xor.stack_seps _).2.1 (by decide),
    Mem.readW_writeW_sep (VG.Proof.ChaCha20.X86.Xor.stack_seps _).2.2 (by decide), Mem.readW_writeW_self32, hd]

theorem entry_esp64 : ((VG.Proof.ChaCha20.X86.Xor.entry s).gpr .esp).setWidth 64 = VG.Proof.ChaCha20.X86.Xor.Es s₀ - 12 := by
  rw [VG.Proof.ChaCha20.X86.Xor.entry_esp]; exact (VG.Proof.ChaCha20.X86.Xor.entry_addrs hp hE).2.2

theorem entry_esp_fit : ((VG.Proof.ChaCha20.X86.Xor.entry s).gpr .esp).toNat + 12 ≤ 2 ^ 32 := by
  have hlo := hp.sp_lo
  rw [VG.Proof.ChaCha20.X86.Xor.entry_esp, hE, show VG.Proof.ChaCha20.X86.Xor.E s₀ - BitVec.ofNat 32 8 - 4 = VG.Proof.ChaCha20.X86.Xor.E s₀ - BitVec.ofNat 32 12 by
    rw [BitVec.sub_sub]; rfl,
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def, VG.Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by lit_omega)]; omega),
    VG.Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by lit_omega)]
  have := (VG.Proof.ChaCha20.X86.Xor.E s₀).isLt
  omega

end

/-- The block function's precondition, from the facts about its entry state. -/
theorem pre_block_of {s₀ s' : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) (h₀ : arg s' 0 = VG.Proof.ChaCha20.X86.Xor.ST s₀) (h₁ : arg s' 1 = VG.Proof.ChaCha20.X86.Xor.BP s₀)
    (ha : argAddr s' 0 = VG.Proof.ChaCha20.X86.Xor.Es s₀ - 8) (hr : (s'.gpr .esp).setWidth 64 = VG.Proof.ChaCha20.X86.Xor.Es s₀ - 12)
    (ht : (s'.gpr .esp).toNat + 12 ≤ 2 ^ 32) (hrd : s'.rd = VG.Proof.ChaCha20.X86.Xor.rdC s₀) (hwr : s'.wr = VG.Proof.ChaCha20.X86.Xor.wrC s₀) :
    Proof.ChaCha20.blockX86.pre s' := by
  show s'.rd = [⟨(arg s' 0).setWidth 64, 64⟩, ⟨argAddr s' 0, 8⟩] ∧
    s'.wr = [⟨(arg s' 1).setWidth 64, 256⟩] ∧
    Region.Disjoint ⟨(arg s' 1).setWidth 64, 256⟩ ⟨(arg s' 0).setWidth 64, 64⟩ ∧
    Region.Disjoint ⟨argAddr s' 0, 8⟩ ⟨(arg s' 1).setWidth 64, 256⟩ ∧
    Region.Disjoint ⟨(s'.gpr .esp).setWidth 64, 4⟩ ⟨(arg s' 1).setWidth 64, 256⟩ ∧
    (arg s' 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s' 1).toNat + 256 ≤ 2 ^ 32 ∧
    (s'.gpr .esp).toNat + 12 ≤ 2 ^ 32
  rw [h₀, h₁, ha, hr]
  exact ⟨hrd, hwr, (hp.st_b.sub_right (VG.Proof.ChaCha20.X86.Xor.b256_sub s₀)).symm,
    (hp.stk_b.sub_left (VG.Proof.ChaCha20.X86.Xor.fR_sub s₀)).sub_right (VG.Proof.ChaCha20.X86.Xor.b256_sub s₀),
    (hp.stk_b.sub_left (VG.Proof.ChaCha20.X86.Xor.cR_sub s₀)).sub_right (VG.Proof.ChaCha20.X86.Xor.b256_sub s₀), hp.st_fit,
    by have := hp.b_fit; omega, ht⟩

/-- The block function's precondition holds when it is called. -/
theorem entry_pre {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {s : State} (hE : s.gpr .esp = VG.Proof.ChaCha20.X86.Xor.E s₀)
    (hb : s.gpr .ebx = VG.Proof.ChaCha20.X86.Xor.ST s₀) (hd : s.gpr .edi = VG.Proof.ChaCha20.X86.Xor.BP s₀) :
    Proof.ChaCha20.blockX86.pre ((VG.Proof.ChaCha20.X86.Xor.entry s).withRegions (VG.Proof.ChaCha20.X86.Xor.rdC s₀) (VG.Proof.ChaCha20.X86.Xor.wrC s₀)) :=
  VG.Proof.ChaCha20.X86.Xor.pre_block_of (s' := (VG.Proof.ChaCha20.X86.Xor.entry s).withRegions (VG.Proof.ChaCha20.X86.Xor.rdC s₀) (VG.Proof.ChaCha20.X86.Xor.wrC s₀)) hp (VG.Proof.ChaCha20.X86.Xor.entry_arg0 (s := s) hp hE hb)
    (VG.Proof.ChaCha20.X86.Xor.entry_arg1 (s := s) hp hE hd) (VG.Proof.ChaCha20.X86.Xor.entry_argAddr0 (s := s) hp hE) (VG.Proof.ChaCha20.X86.Xor.entry_esp64 (s := s) hp hE)
    (VG.Proof.ChaCha20.X86.Xor.entry_esp_fit (s := s) hp hE) rfl rfl

/-- After the block function: `buf` holds block `j`'s keystream. -/
structure AInv (s₀ : State) (j : Nat) (s : State) : Prop extends VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s where
  ks : ∀ t < 64, s.mem (VG.Proof.ChaCha20.X86.Xor.bp s₀ + BitVec.ofNat 64 t) =
    (serialize (Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.X86.Xor.S0 s₀) j))).getD t 0

theorem pushed_wr_eq {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {s : State} (hE : s.gpr .esp = VG.Proof.ChaCha20.X86.Xor.E s₀) :
    (pushed [.edi, .ebx] s).wr = VG.Proof.ChaCha20.X86.Xor.fR s₀ :: s.wr := by
  have hlo := hp.sp_lo
  rw [pushed_wr, hE]
  show below (VG.Proof.ChaCha20.X86.Xor.E s₀) 8 :: s.wr = _
  simp only [below]
  rw [VG.Proof.ChaCha20.X86.Xor.setWidth_sub (by lit_omega)]; rfl

theorem call_covers {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {s : State} (hE : s.gpr .esp = VG.Proof.ChaCha20.X86.Xor.E s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    Covers (VG.Proof.ChaCha20.X86.Xor.rdC s₀ ++ VG.Proof.ChaCha20.X86.Xor.wrC s₀) ((pushed [.edi, .ebx] s).rd ++ (pushed [.edi, .ebx] s).wr) ∧
      Covers (VG.Proof.ChaCha20.X86.Xor.wrC s₀) (pushed [.edi, .ebx] s).wr := by
  rw [pushed_rd, VG.Proof.ChaCha20.X86.Xor.pushed_wr_eq hp hE, hrd, hwr, hp.rd, hp.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.ChaCha20.X86.Xor.stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 64 by omega⟩
    · exact ⟨VG.Proof.ChaCha20.X86.Xor.fR s₀, by simp, 0, by simp, show 0 + 8 ≤ 8 by omega⟩
    · exact ⟨VG.Proof.ChaCha20.X86.Xor.bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨VG.Proof.ChaCha20.X86.Xor.bR s₀, by simp, 0, by simp, show 0 + 256 ≤ 320 by omega⟩

/-! ### The frame's pop -/

theorem popped_esp (r : Reg) (k : Nat) (s : State) :
    (popped r k s).gpr .esp = s.gpr .esp + BitVec.ofNat 32 (4 * k) := (popReg_eq s r k).2.2.1

theorem popped_gpr (r : Reg) (k : Nat) (s : State) {q : Reg} (h₁ : q ≠ .esp) (h₂ : q ≠ r) :
    (popped r k s).gpr q = s.gpr q := (popReg_eq s r k).2.2.2 q h₁ h₂

theorem popped_rd (r : Reg) (k : Nat) (s : State) : (popped r k s).rd = s.rd := (popReg_eq s r k).1

theorem popped_wr (r : Reg) (k : Nat) (s : State) : (popped r k s).wr = s.wr.tail := rfl

theorem popped_mem (r : Reg) (k : Nat) (s : State) : (popped r k s).mem = s.mem :=
  (popReg_rest s r k).1

/-! ### The call -/

theorem block_nosp : NoSp Impl.ChaCha20.X86.block := by
  have : ((instrs Impl.ChaCha20.X86.block).all fun i => !Taint.clobbers i .esp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp this i hi

theorem block_stackUse : stackUse Impl.ChaCha20.X86.block = 0 := by lit_decide

theorem stackR_eq {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) : VG.Proof.ChaCha20.X86.Xor.stackR s₀ = below (VG.Proof.ChaCha20.X86.Xor.E s₀) 12 := by
  simp only [VG.Proof.ChaCha20.X86.Xor.stackR, below]
  rw [VG.Proof.ChaCha20.X86.Xor.setWidth_sub hp.sp_lo]
  rfl

theorem call_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.X86.Xor.P s₀ j < VG.Proof.ChaCha20.X86.Xor.L s₀) {s : State} (h : VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s) :
    WP isa callBlock s (VG.Proof.ChaCha20.X86.Xor.AInv s₀ j) := by
  have hlo := hp.sp_lo
  obtain ⟨hc, hw⟩ := VG.Proof.ChaCha20.X86.Xor.call_covers hp h.esp h.rd h.wr
  have hn : 4 * [Reg.edi, .ebx].length ≤ (s.gpr .esp).toNat := by
    rw [h.esp]; simp only [List.length_cons, List.length_nil]; omega
  have hd : stackUse Impl.ChaCha20.X86.block + 4 ≤ ((pushed [.edi, .ebx] s).gpr .esp).toNat := by
    rw [VG.Proof.ChaCha20.X86.Xor.block_stackUse, pushed_esp, sub_toNat hn, h.esp]
    simp only [List.length_cons, List.length_nil]; omega
  refine WP.frame (rs := [.edi, .ebx]) (r := .eax) (by simp) (by decide) (by decide) hn VG.Proof.ChaCha20.X86.Xor.block_nosp ?_
  refine WP.call (k := Proof.ChaCha20.blockX86) VG.Proof.ChaCha20.X86.block_correct VG.Proof.ChaCha20.X86.Xor.block_nosp hd (rd := VG.Proof.ChaCha20.X86.Xor.rdC s₀)
    (wr := VG.Proof.ChaCha20.X86.Xor.wrC s₀) (VG.Proof.ChaCha20.X86.Xor.entry_pre hp h.esp h.ebx h.edi) hc hw
    fun s' hrd hwr hcs hf _ ⟨s₂, hm₂, _, hpost⟩ => ?_
  have hsp : s'.gpr .esp = (pushed [.edi, .ebx] s).gpr .esp := hcs .esp (by simp [calleeSaved])
  -- The frame, the return address and the block function's writes.
  have hF : Frame [VG.Proof.ChaCha20.X86.Xor.b256 s₀, VG.Proof.ChaCha20.X86.Xor.stackR s₀] s.mem s'.mem := by
    rw [VG.Proof.ChaCha20.X86.Xor.stackR_eq hp]
    refine (Frame.sub (pushed_frame (by decide) hn) fun r hr => ?_).trans (Frame.sub hf fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨below (VG.Proof.ChaCha20.X86.Xor.E s₀) 12, by simp, by rw [h.esp]; exact below_sub (by decide) hlo⟩
    · simp only [VG.Proof.ChaCha20.X86.Xor.wrC, VG.Proof.ChaCha20.X86.Xor.block_stackUse, List.cons_append, List.nil_append, List.mem_cons,
        List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.X86.Xor.b256 s₀, by simp, fun _ h => h⟩
      · refine ⟨below (VG.Proof.ChaCha20.X86.Xor.E s₀) 12, by simp, ?_⟩
        rw [pushed_esp, h.esp]
        exact below_inner (by decide) hlo
  have hd : ∀ R : Region, R.Disjoint (VG.Proof.ChaCha20.X86.Xor.b256 s₀) → R.Disjoint (VG.Proof.ChaCha20.X86.Xor.stackR s₀) →
      ∀ r ∈ [VG.Proof.ChaCha20.X86.Xor.b256 s₀, VG.Proof.ChaCha20.X86.Xor.stackR s₀], R.Disjoint r := by
    intro R h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  have hst : stateAt s'.mem (VG.Proof.ChaCha20.X86.Xor.st s₀) = stateAt s.mem (VG.Proof.ChaCha20.X86.Xor.st s₀) :=
    VG.Proof.ChaCha20.X86.Xor.stateAt_frame hF (hd _ (hp.st_b.sub_right (VG.Proof.ChaCha20.X86.Xor.b256_sub s₀)) hp.stk_st.symm)
  have g : ∀ r ∈ calleeSaved, r ≠ .esp → r ≠ .eax → (popped .eax [Reg.edi, .ebx].length s').gpr r = s.gpr r := by
    intro r hr h₁ h₂
    rw [VG.Proof.ChaCha20.X86.Xor.popped_gpr _ _ _ h₁ h₂, hcs r hr, pushed_gpr _ _ h₁]
  have e0 : arg ((VG.Proof.ChaCha20.X86.Xor.entry s).withRegions (VG.Proof.ChaCha20.X86.Xor.rdC s₀) (VG.Proof.ChaCha20.X86.Xor.wrC s₀)) 0 = VG.Proof.ChaCha20.X86.Xor.ST s₀ := VG.Proof.ChaCha20.X86.Xor.entry_arg0 (s := s) hp h.esp h.ebx
  have e1 : arg ((VG.Proof.ChaCha20.X86.Xor.entry s).withRegions (VG.Proof.ChaCha20.X86.Xor.rdC s₀) (VG.Proof.ChaCha20.X86.Xor.wrC s₀)) 1 = VG.Proof.ChaCha20.X86.Xor.BP s₀ := VG.Proof.ChaCha20.X86.Xor.entry_arg1 (s := s) hp h.esp h.edi
  have hpost' : stateAt s'.mem (VG.Proof.ChaCha20.X86.Xor.bp s₀) = Spec.ChaCha20.block (ctr (VG.Proof.ChaCha20.X86.Xor.S0 s₀) j) := by
    have := (show stateAt s₂.mem ((arg ((VG.Proof.ChaCha20.X86.Xor.entry s).withRegions (VG.Proof.ChaCha20.X86.Xor.rdC s₀) (VG.Proof.ChaCha20.X86.Xor.wrC s₀)) 1).setWidth 64) =
      Spec.ChaCha20.block (stateAt ((VG.Proof.ChaCha20.X86.Xor.entry s).withRegions (VG.Proof.ChaCha20.X86.Xor.rdC s₀) (VG.Proof.ChaCha20.X86.Xor.wrC s₀)).mem
        ((arg ((VG.Proof.ChaCha20.X86.Xor.entry s).withRegions (VG.Proof.ChaCha20.X86.Xor.rdC s₀) (VG.Proof.ChaCha20.X86.Xor.wrC s₀)) 0).setWidth 64)) from hpost)
    rw [e0, e1, hm₂, State.withRegions_mem,
      VG.Proof.ChaCha20.X86.Xor.stateAt_frame (VG.Proof.ChaCha20.X86.Xor.entry_frame hp h.esp) (by simpa using hp.stk_st.symm), h.cnt hj] at this
    exact this
  refine ⟨⟨by rw [g .ebx (by simp [calleeSaved]) (by decide) (by decide), h.ebx],
    by rw [g .esi (by simp [calleeSaved]) (by decide) (by decide), h.esi],
    by rw [g .edi (by simp [calleeSaved]) (by decide) (by decide), h.edi],
    by rw [g .ebp (by simp [calleeSaved]) (by decide) (by decide), h.ebp],
    ?_, by rw [VG.Proof.ChaCha20.X86.Xor.popped_rd, hrd, pushed_rd, h.rd],
    by rw [VG.Proof.ChaCha20.X86.Xor.popped_wr, hwr, VG.Proof.ChaCha20.X86.Xor.pushed_wr_eq hp h.esp, List.tail_cons, h.wr],
    fun _ => by rw [VG.Proof.ChaCha20.X86.Xor.popped_mem, hst, h.cnt hj], fun k hk => ?_, ?_, ?_⟩, fun t ht => ?_⟩
  · rw [VG.Proof.ChaCha20.X86.Xor.popped_esp, hsp, pushed_esp, h.esp]
    simp only [List.length_cons, List.length_nil]
    exact BitVec.sub_add_cancel _ _
  · rw [VG.Proof.ChaCha20.X86.Xor.popped_mem, hF.bytes (R := VG.Proof.ChaCha20.X86.Xor.dR s₀) (hd _ (hp.d_b.sub_right (VG.Proof.ChaCha20.X86.Xor.b256_sub s₀)) hp.stk_d.symm)
      (show VG.Proof.ChaCha20.X86.Xor.L s₀ ≤ 2 ^ 64 by have := VG.Proof.ChaCha20.X86.Xor.L_lt s₀; omega) hk]
    exact h.data k hk
  · rw [VG.Proof.ChaCha20.X86.Xor.popped_mem]
    exact h.saved.frame hF (hd _ (VG.Proof.ChaCha20.X86.Xor.savR_b256 s₀) (hp.stk_b.symm.sub_left (VG.Proof.ChaCha20.X86.Xor.savR_sub s₀)))
  · rw [VG.Proof.ChaCha20.X86.Xor.popped_mem]
    exact h.frame.trans (hF.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨VG.Proof.ChaCha20.X86.Xor.bR s₀, by simp, VG.Proof.ChaCha20.X86.Xor.b256_sub s₀⟩
      · exact ⟨VG.Proof.ChaCha20.X86.Xor.stackR s₀, by simp, fun _ h => h⟩)
  · rw [VG.Proof.ChaCha20.X86.Xor.popped_mem, ← serialize_stateAt s'.mem (VG.Proof.ChaCha20.X86.Xor.bp s₀) ht, hpost']

theorem P_le (s₀ : State) (j : Nat) : VG.Proof.ChaCha20.X86.Xor.P s₀ j ≤ VG.Proof.ChaCha20.X86.Xor.L s₀ := Nat.min_le_right _ _

/-! ## The end of a block -/

/-- The state after its counter (word 12) is stored. -/
theorem stateAt_writeW_counter (m : Mem) (p : Addr) (v : BitVec 32) :
    stateAt (m.writeW (p + BitVec.ofNat 64 48) v) p = (stateAt m p).set 12 v := by
  apply Vector.ext
  intro i hi
  simp only [stateAt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : 12 = i
  · subst h
    simp only [ite_true]
    exact Mem.readW_writeW_self32 _ _ _
  · simp only [h, ite_false]
    exact VG.Proof.ChaCha20.X86.readW_writeW_off m p v (by lit_omega) (by lit_omega) (by lit_omega)

/-! ## Four blocks at once -/

section Quad
open Quad (dW slotsR ctrR)

theorem ctx_of {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {s : State} (hb : s.gpr .ebx = VG.Proof.ChaCha20.X86.Xor.ST s₀)
    (hd : s.gpr .edi = VG.Proof.ChaCha20.X86.Xor.BP s₀) (hw : s.wr = s₀.wr) : Quad.Ctx (VG.Proof.ChaCha20.X86.Xor.st s₀) (VG.Proof.ChaCha20.X86.Xor.bp s₀) s :=
  ⟨fun d h => by show addr (s.gpr .ebx) d = _; rw [hb]; exact hp.eaS h,
   fun d h => by show addr (s.gpr .edi) d = _; rw [hd]; exact hp.eaB h,
   by rw [hw, hp.wr]; simp, by rw [hw, hp.wr]; simp, hp.st_b⟩

theorem ptr_add2 (x : BitVec 32) {k d : Nat} (h : x.toNat + k + d < 2 ^ 32) :
    (x + BitVec.ofNat 32 k + BitVec.ofNat 32 d).setWidth 64 =
      x.setWidth 64 + BitVec.ofNat 64 k + BitVec.ofNat 64 d := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The data of the four blocks after `j`. -/
abbrev win (s₀ : State) (j : Nat) : Addr := VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86.Xor.P s₀ j)

/-- How many bytes of data the four blocks after `j` are for. -/
abbrev Wn (s₀ : State) (j : Nat) : Nat := min (VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ j) 256

theorem Wn_le (s₀ : State) (j : Nat) : VG.Proof.ChaCha20.X86.Xor.Wn s₀ j ≤ VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ j ∧ VG.Proof.ChaCha20.X86.Xor.Wn s₀ j ≤ 256 :=
  ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩

theorem dctx_of {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {j : Nat} {s : State}
    (hsi : s.gpr .esi = VG.Proof.ChaCha20.X86.Xor.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Xor.P s₀ j)) (hw : s.wr = s₀.wr) :
    Quad.DCtx (VG.Proof.ChaCha20.X86.Xor.win s₀ j) (VG.Proof.ChaCha20.X86.Xor.Wn s₀ j) s :=
  ⟨fun d h => by
      show addr (s.gpr .esi) d = _
      rw [hsi]; exact VG.Proof.ChaCha20.X86.Xor.ptr_add2 _ (by have := hp.d_fit; have := VG.Proof.ChaCha20.X86.Xor.P_le s₀ j; have := VG.Proof.ChaCha20.X86.Xor.Wn_le s₀ j; omega),
   fun off n h => ⟨VG.Proof.ChaCha20.X86.Xor.dR s₀, by rw [hw, hp.wr]; simp, by
      have := VG.Proof.ChaCha20.X86.Xor.L_lt s₀
      have := VG.Proof.ChaCha20.X86.Xor.P_le s₀ j
      have := VG.Proof.ChaCha20.X86.Xor.Wn_le s₀ j
      rw [Offset.add_add]; exact VG.Proof.ChaCha20.X86.Xor.contains_ofNat (by omega) (by lit_omega)⟩⟩

theorem ctr_ctr (S : CState) (a b : Nat) : ctr (ctr S a) b = ctr S (a + b) := by
  simp only [ctr, Vector.set_set, Vector.getElem_set_self, BitVec.ofNat_add, BitVec.add_assoc]

theorem ctr_add (S : CState) (j n : Nat) :
    (ctr S j).set 12 ((ctr S j)[12] + BitVec.ofNat 32 n) = ctr S (j + n) := by
  rw [← VG.Proof.ChaCha20.X86.Xor.ctr_ctr]; rfl

/-- The regions four blocks write: the slots, the counters and `buf[0, 16)`
in `buf`, the data of the four blocks, and the state (its counter). -/
abbrev qR (s₀ : State) (j : Nat) : List Region :=
  [VG.Proof.ChaCha20.X86.Quad.slotsR (VG.Proof.ChaCha20.X86.Xor.bp s₀), VG.Proof.ChaCha20.X86.Quad.ctrR (VG.Proof.ChaCha20.X86.Xor.bp s₀), VG.Proof.ChaCha20.X86.Quad.dW (VG.Proof.ChaCha20.X86.Xor.win s₀ j) (VG.Proof.ChaCha20.X86.Xor.Wn s₀ j), Quad.stashR (VG.Proof.ChaCha20.X86.Xor.bp s₀), VG.Proof.ChaCha20.X86.Xor.stR s₀]

theorem slots_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86.Quad.slotsR (VG.Proof.ChaCha20.X86.Xor.bp s₀)) (VG.Proof.ChaCha20.X86.Xor.bR s₀) := Region.sub_prefix (by decide)
theorem ctrR_sub (s₀ : State) : Region.Sub (VG.Proof.ChaCha20.X86.Quad.ctrR (VG.Proof.ChaCha20.X86.Xor.bp s₀)) (VG.Proof.ChaCha20.X86.Xor.bR s₀) := Offset.sub_base _ (by decide)
theorem stash_sub (s₀ : State) : Region.Sub (Quad.stashR (VG.Proof.ChaCha20.X86.Xor.bp s₀)) (VG.Proof.ChaCha20.X86.Xor.bR s₀) := Region.sub_prefix (by decide)
theorem dW_sub (s₀ : State) (j : Nat) : Region.Sub (VG.Proof.ChaCha20.X86.Quad.dW (VG.Proof.ChaCha20.X86.Xor.win s₀ j) (VG.Proof.ChaCha20.X86.Xor.Wn s₀ j)) (VG.Proof.ChaCha20.X86.Xor.dR s₀) :=
  Offset.sub_base _ (by have := VG.Proof.ChaCha20.X86.Xor.P_le s₀ j; have := VG.Proof.ChaCha20.X86.Xor.Wn_le s₀ j; omega)

theorem qR_frame (s₀ : State) (j : Nat) : ∀ r ∈ VG.Proof.ChaCha20.X86.Xor.qR s₀ j, ∃ r' ∈ VG.Proof.ChaCha20.X86.Xor.frameR s₀, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨VG.Proof.ChaCha20.X86.Xor.bR s₀, by simp, VG.Proof.ChaCha20.X86.Xor.slots_sub s₀⟩
  · exact ⟨VG.Proof.ChaCha20.X86.Xor.bR s₀, by simp, VG.Proof.ChaCha20.X86.Xor.ctrR_sub s₀⟩
  · exact ⟨VG.Proof.ChaCha20.X86.Xor.dR s₀, by simp, VG.Proof.ChaCha20.X86.Xor.dW_sub s₀ j⟩
  · exact ⟨VG.Proof.ChaCha20.X86.Xor.bR s₀, by simp, VG.Proof.ChaCha20.X86.Xor.stash_sub s₀⟩
  · exact ⟨VG.Proof.ChaCha20.X86.Xor.stR s₀, by simp, fun _ h => h⟩

theorem qR_saved {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) (j : Nat) : ∀ r ∈ VG.Proof.ChaCha20.X86.Xor.qR s₀ j, (VG.Proof.ChaCha20.X86.Xor.savR s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact Offset.disjoint _ (by simp only [ctrOff]; omega) (by decide) (by decide)
  · exact (hp.d_b.symm.sub_left (VG.Proof.ChaCha20.X86.Xor.savR_sub s₀)).sub_right (VG.Proof.ChaCha20.X86.Xor.dW_sub s₀ j)
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact (hp.st_b.symm.sub_left (VG.Proof.ChaCha20.X86.Xor.savR_sub s₀))

/-- The keystream of the four blocks after `j`: the rounds' result plus the
input states, the counter being block `j`'s. -/
abbrev B4 (C : CState) : Nat → CState :=
  Quad.blk (fun l => Nat.repeat Spec.ChaCha20.innerBlock 10 (ctr C l)) C

theorem ksb_eq {s₀ : State} {j t : Nat} (hPj : VG.Proof.ChaCha20.X86.Xor.P s₀ j = 64 * j) (ht : VG.Proof.ChaCha20.X86.Xor.P s₀ j + t < VG.Proof.ChaCha20.X86.Xor.L s₀) :
    Quad.ksb (VG.Proof.ChaCha20.X86.Xor.B4 (ctr (VG.Proof.ChaCha20.X86.Xor.S0 s₀) j)) t = (VG.Proof.ChaCha20.X86.Xor.KS s₀).getD (VG.Proof.ChaCha20.X86.Xor.P s₀ j + t) 0 := by
  show (serialize (Spec.ChaCha20.block (ctr (ctr (VG.Proof.ChaCha20.X86.Xor.S0 s₀) j) (t / 64)))).getD (t % 64) 0 = _
  rw [VG.Proof.ChaCha20.X86.Xor.KS, keystream_getD _ ht, VG.Proof.ChaCha20.X86.Xor.ctr_ctr, hPj, show j + t / 64 = (64 * j + t) / 64 by omega,
    show t % 64 = (64 * j + t) % 64 by omega]

/-- What the setup, the rounds and the output leave: the keystream XORed
into the data (but for the bytes past the last multiple of 16, if any, whose
keystream is in `buf[0, 16)`), and everything else as it was but `eax` and
the regions of `qR` (not the state). -/
structure Q4 (s₀ : State) (j : Nat) (s s' : State) : Prop where
  data : ∀ k, k < VG.Proof.ChaCha20.X86.Xor.Wn s₀ j → s'.mem (VG.Proof.ChaCha20.X86.Xor.win s₀ j + BitVec.ofNat 64 k) =
    if Quad.Full (VG.Proof.ChaCha20.X86.Xor.Wn s₀ j) k then
      s.mem (VG.Proof.ChaCha20.X86.Xor.win s₀ j + BitVec.ofNat 64 k) ^^^ Quad.ksb (VG.Proof.ChaCha20.X86.Xor.B4 (stateAt s.mem (VG.Proof.ChaCha20.X86.Xor.st s₀))) k
    else s.mem (VG.Proof.ChaCha20.X86.Xor.win s₀ j + BitVec.ofNat 64 k)
  stash : Quad.Stashed (VG.Proof.ChaCha20.X86.Xor.bp s₀) (VG.Proof.ChaCha20.X86.Xor.B4 (stateAt s.mem (VG.Proof.ChaCha20.X86.Xor.st s₀))) (VG.Proof.ChaCha20.X86.Xor.Wn s₀ j) (fun _ => True) s'.mem
  keep : ∀ r, r ≠ .eax → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame [VG.Proof.ChaCha20.X86.Quad.slotsR (VG.Proof.ChaCha20.X86.Xor.bp s₀), VG.Proof.ChaCha20.X86.Quad.ctrR (VG.Proof.ChaCha20.X86.Xor.bp s₀), VG.Proof.ChaCha20.X86.Quad.dW (VG.Proof.ChaCha20.X86.Xor.win s₀ j) (VG.Proof.ChaCha20.X86.Xor.Wn s₀ j), Quad.stashR (VG.Proof.ChaCha20.X86.Xor.bp s₀)] s.mem s'.mem
  st : stateAt s'.mem (VG.Proof.ChaCha20.X86.Xor.st s₀) = stateAt s.mem (VG.Proof.ChaCha20.X86.Xor.st s₀)

theorem kR_sub (s₀ : State) : Region.Sub (Quad.kR (VG.Proof.ChaCha20.X86.Xor.bp s₀)) (VG.Proof.ChaCha20.X86.Xor.bR s₀) := Offset.sub_base _ (by decide)

/-- What the four blocks write is outside `buf[288, 320)`. -/
theorem kR_qR {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) (j : Nat) : ∀ r ∈ VG.Proof.ChaCha20.X86.Xor.qR s₀ j, (Quad.kR (VG.Proof.ChaCha20.X86.Xor.bp s₀)).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact Quad.kR_slots _
  · exact Offset.disjoint _ (by simp only [ctrOff]; omega) (by decide) (by decide)
  · exact (hp.d_b.symm.sub_left (VG.Proof.ChaCha20.X86.Xor.kR_sub s₀)).sub_right (VG.Proof.ChaCha20.X86.Xor.dW_sub s₀ j)
  · exact Offset.disjoint_base _ (by decide) (by decide)
  · exact hp.st_b.symm.sub_left (VG.Proof.ChaCha20.X86.Xor.kR_sub s₀)

theorem quad4_ok {k : Kernel} (Kk : Quad.KernelOk k) {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {j : Nat}
    (hj : VG.Proof.ChaCha20.X86.Xor.P s₀ j + 65 ≤ VG.Proof.ChaCha20.X86.Xor.L s₀) {s : State} (h : VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s) (hinv : Kk.Inv (VG.Proof.ChaCha20.X86.Xor.bp s₀) s.mem)
    {C : Prog isa} {Q : State → Prop} (hk : ∀ s₃, VG.Proof.ChaCha20.X86.Xor.Q4 s₀ j s s₃ → WP isa C s₃ Q) :
    WP isa (.seq (.block setup4) (.seq (rounds10 k) (.seq finish4 C))) s Q := by
  have hL := VG.Proof.ChaCha20.X86.Xor.L_lt s₀
  have hc := VG.Proof.ChaCha20.X86.Xor.ctx_of hp h.ebx h.edi h.wr
  have sl_st : (VG.Proof.ChaCha20.X86.Xor.stR s₀).Disjoint (VG.Proof.ChaCha20.X86.Quad.slotsR (VG.Proof.ChaCha20.X86.Xor.bp s₀)) := hp.st_b.sub_right (VG.Proof.ChaCha20.X86.Xor.slots_sub s₀)
  have ct_st : (VG.Proof.ChaCha20.X86.Xor.stR s₀).Disjoint (VG.Proof.ChaCha20.X86.Quad.ctrR (VG.Proof.ChaCha20.X86.Xor.bp s₀)) := hp.st_b.sub_right (VG.Proof.ChaCha20.X86.Xor.ctrR_sub s₀)
  have db : (VG.Proof.ChaCha20.X86.Quad.dW (VG.Proof.ChaCha20.X86.Xor.win s₀ j) (VG.Proof.ChaCha20.X86.Xor.Wn s₀ j)).Disjoint (Quad.bufR (VG.Proof.ChaCha20.X86.Xor.bp s₀)) := hp.d_b.sub_left (VG.Proof.ChaCha20.X86.Xor.dW_sub s₀ j)
  have ds : (VG.Proof.ChaCha20.X86.Quad.dW (VG.Proof.ChaCha20.X86.Xor.win s₀ j) (VG.Proof.ChaCha20.X86.Xor.Wn s₀ j)).Disjoint (Quad.stR (VG.Proof.ChaCha20.X86.Xor.st s₀)) := hp.st_d.symm.sub_left (VG.Proof.ChaCha20.X86.Xor.dW_sub s₀ j)
  -- The setup.
  refine WP.seq (WP.mono (Quad.setup4_ok hc) fun s₁ h₁ => ?_)
  have hc₁ : Quad.Ctx (VG.Proof.ChaCha20.X86.Xor.st s₀) (VG.Proof.ChaCha20.X86.Xor.bp s₀) s₁ := VG.Proof.ChaCha20.X86.Xor.ctx_of hp (by rw [h₁.keep _ (by decide), h.ebx])
    (by rw [h₁.keep _ (by decide), h.edi]) (by rw [h₁.wr, h.wr])
  -- The rounds.
  refine WP.seq (WP.mono (Quad.rounds_ok hc₁.eaB hc₁.wb Kk (Kk.inv_frame hinv h₁.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.Proof.ChaCha20.X86.Xor.kR_qR hp j _ (by simp)
      · exact VG.Proof.ChaCha20.X86.Xor.kR_qR hp j _ (by simp))) h₁.holds) fun s₂ h₂ => ?_)
  have hc₂ : Quad.Ctx (VG.Proof.ChaCha20.X86.Xor.st s₀) (VG.Proof.ChaCha20.X86.Xor.bp s₀) s₂ := hc₁.of h₂.gpr h₂.wr
  have hg₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr => by rw [h₂.gpr, h₁.keep r hr]
  have hd₂ : Quad.DCtx (VG.Proof.ChaCha20.X86.Xor.win s₀ j) (VG.Proof.ChaCha20.X86.Xor.Wn s₀ j) s₂ := VG.Proof.ChaCha20.X86.Xor.dctx_of hp (by rw [hg₂ _ (by decide), h.esi])
    (by rw [h₂.wr, h₁.wr, h.wr])
  have hct₂ : Quad.Ctrs (VG.Proof.ChaCha20.X86.Xor.bp s₀) (stateAt s.mem (VG.Proof.ChaCha20.X86.Xor.st s₀)) 4 s₂.mem := fun l hl => by
    rw [h₂.frame.readW (r := VG.Proof.ChaCha20.X86.Quad.ctrR (VG.Proof.ChaCha20.X86.Xor.bp s₀)) (Offset.contains _ (by omega) (by omega) (by decide))
      (by simp only [List.mem_singleton, forall_eq]; exact Offset.disjoint_base _ (by decide) (by decide))
      (by decide)]
    exact h₁.ctrs l hl
  have hC₂ : stateAt s₂.mem (VG.Proof.ChaCha20.X86.Xor.st s₀) = stateAt s.mem (VG.Proof.ChaCha20.X86.Xor.st s₀) :=
    (Quad.stateAt_frame h₂.frame (by simpa using sl_st)).trans
      (Quad.stateAt_frame h₁.frame (by simpa using ⟨sl_st, ct_st⟩))
  -- The output.
  refine WP.seq (WP.mono (Quad.finish4_ok hc₂ hd₂ (VG.Proof.ChaCha20.X86.Xor.L_lt s₀ |> fun h' => by omega) rfl
    (by rw [hg₂ _ (by decide), h.ebp]) db ds h₂.holds hct₂ hC₂) fun s₃ h₃ => hk s₃ ?_)
  have hf₃ : Frame [VG.Proof.ChaCha20.X86.Quad.slotsR (VG.Proof.ChaCha20.X86.Xor.bp s₀), VG.Proof.ChaCha20.X86.Quad.ctrR (VG.Proof.ChaCha20.X86.Xor.bp s₀), VG.Proof.ChaCha20.X86.Quad.dW (VG.Proof.ChaCha20.X86.Xor.win s₀ j) (VG.Proof.ChaCha20.X86.Xor.Wn s₀ j), Quad.stashR (VG.Proof.ChaCha20.X86.Xor.bp s₀)] s.mem s₃.mem :=
    ((h₁.frame.mono (by simp)).trans (h₂.frame.mono (by simp))).trans (h₃.frame.mono (by simp))
  have hW : VG.Proof.ChaCha20.X86.Xor.Wn s₀ j ≤ 256 := Nat.min_le_right _ _
  refine ⟨fun k hk => ?_, fun hz _ => h₃.stash hz (by simp only [Quad.sOff]; omega),
    fun r hr => by rw [h₃.gpr, hg₂ r hr], by rw [h₃.rd, h₂.rd, h₁.rd], by rw [h₃.wr, h₂.wr, h₁.wr], hf₃, ?_⟩
  · have e₂ : s₂.mem (VG.Proof.ChaCha20.X86.Xor.win s₀ j + BitVec.ofNat 64 k) = s.mem (VG.Proof.ChaCha20.X86.Xor.win s₀ j + BitVec.ofNat 64 k) :=
      (h₁.frame.trans (h₂.frame.mono (by simp))).bytes (R := VG.Proof.ChaCha20.X86.Quad.dW (VG.Proof.ChaCha20.X86.Xor.win s₀ j) (VG.Proof.ChaCha20.X86.Xor.Wn s₀ j))
        (by simpa using ⟨db.sub_right (VG.Proof.ChaCha20.X86.Xor.slots_sub s₀), db.sub_right (VG.Proof.ChaCha20.X86.Xor.ctrR_sub s₀)⟩)
        (show VG.Proof.ChaCha20.X86.Xor.Wn s₀ j ≤ 2 ^ 64 by omega) hk
    rw [h₃.data k hk, e₂]
    by_cases c : Quad.Full (VG.Proof.ChaCha20.X86.Xor.Wn s₀ j) k
    · rw [ite_eq_left ⟨by omega, c⟩, ite_eq_left c]
    · rw [ite_eq_right (by omega), ite_eq_right c]
  · exact Quad.stateAt_frame hf₃ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact sl_st
      · exact ct_st
      · exact ds.symm
      · exact hp.st_b.sub_right (VG.Proof.ChaCha20.X86.Xor.stash_sub s₀))

/-- The data before four blocks `j` that `Q4` leaves: what it was, outside
the `W` bytes of the four blocks. -/
theorem Q4.outside {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {j : Nat} {s s₃ : State} (h₃ : VG.Proof.ChaCha20.X86.Xor.Q4 s₀ j s s₃) {k : Nat}
    (hk : k < VG.Proof.ChaCha20.X86.Xor.L s₀) (hw : ¬ (VG.Proof.ChaCha20.X86.Xor.P s₀ j ≤ k ∧ k < VG.Proof.ChaCha20.X86.Xor.P s₀ j + VG.Proof.ChaCha20.X86.Xor.Wn s₀ j)) :
    s₃.mem (VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 k) = s.mem (VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 k) := by
  have hL := VG.Proof.ChaCha20.X86.Xor.L_lt s₀
  have := VG.Proof.ChaCha20.X86.Xor.P_le s₀ j
  have := VG.Proof.ChaCha20.X86.Xor.Wn_le s₀ j
  refine h₃.frame _ fun r hr => ?_
  have hin : (VG.Proof.ChaCha20.X86.Xor.dR s₀).Contains (VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 k) 1 := VG.Proof.ChaCha20.X86.Xor.contains_ofNat (by omega) (by lit_omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (hp.d_b.sub_right (VG.Proof.ChaCha20.X86.Xor.slots_sub s₀)) _ hin
  · exact (hp.d_b.sub_right (VG.Proof.ChaCha20.X86.Xor.ctrR_sub s₀)) _ hin
  · simp only [Region.Contains]
    rw [Offset.sub_toNat' _ (by lit_omega) (by lit_omega)]
    split <;> omega
  · exact (hp.d_b.sub_right (VG.Proof.ChaCha20.X86.Xor.stash_sub s₀)) _ hin

/-- More than 256 bytes left: the counter advanced by 4, and the data by 256 bytes. -/
theorem next_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.X86.Xor.P s₀ j + 257 ≤ VG.Proof.ChaCha20.X86.Xor.L s₀) {s s₃ : State}
    (h : VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s) (h₃ : VG.Proof.ChaCha20.X86.Xor.Q4 s₀ j s s₃) :
    WP isa (.block next4) s₃ fun s' => VG.Proof.ChaCha20.X86.Xor.OInv s₀ (j + 4) s' ∧ Frame [VG.Proof.ChaCha20.X86.Xor.stR s₀] s₃.mem s'.mem := by
  have hL := VG.Proof.ChaCha20.X86.Xor.L_lt s₀
  have hPj : VG.Proof.ChaCha20.X86.Xor.P s₀ j = 64 * j := by simp only [VG.Proof.ChaCha20.X86.Xor.P] at *; omega
  have hP4 : VG.Proof.ChaCha20.X86.Xor.P s₀ (j + 4) = VG.Proof.ChaCha20.X86.Xor.P s₀ j + 256 := by simp only [VG.Proof.ChaCha20.X86.Xor.P] at *; omega
  have hW : VG.Proof.ChaCha20.X86.Xor.Wn s₀ j = 256 := by simp only [VG.Proof.ChaCha20.X86.Xor.Wn]; omega
  have hcnt := h.cnt (by omega)
  unfold next4
  have e48 : addr (VG.Proof.ChaCha20.X86.Xor.ST s₀) 48 = VG.Proof.ChaCha20.X86.Xor.st s₀ + BitVec.ofNat 64 48 := hp.eaS (by decide)
  have i48 : InRegions (s₃.rd ++ s₃.wr) (addr (VG.Proof.ChaCha20.X86.Xor.ST s₀) 48) 4 := by
    rw [e48, h₃.rd, h₃.wr, h.rd, h.wr]
    exact Quad.in_st (by rw [hp.wr]; simp) (by decide)
  refine Wp.wp_ldm (by rw [h₃.keep _ (by decide), h.ebx]) i48 fun s₄ u₄ => ?_
  refine Wp.wp_addi fun s₅ u₅ => ?_
  have o48 : InRegions s₅.wr (addr (VG.Proof.ChaCha20.X86.Xor.ST s₀) 48) 4 := by
    rw [e48, u₅.wr, u₄.wr, h₃.wr, h.wr]
    exact Quad.out_st (by rw [hp.wr]; simp) (by decide)
  refine Wp.wp_stm (by rw [u₅.other _ (by decide), u₄.other _ (by decide), h₃.keep _ (by decide), h.ebx])
    o48 fun s₆ u₆ => ?_
  refine Wp.wp_addi fun s₇ u₇ => ?_
  refine Wp.wp_subi fun s₈ u₈ _ _ => WP.block_nil ?_
  have hg : ∀ r, r ≠ .eax → r ≠ .esi → r ≠ .ebp → s₈.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₈.other r h3, u₇.other r h2, u₆.gpr, u₅.other r h1, u₄.other r h1, h₃.keep r h1]
  have hv : s₃.mem.readW (VG.Proof.ChaCha20.X86.Xor.st s₀ + BitVec.ofNat 64 48) 32 = (ctr (VG.Proof.ChaCha20.X86.Xor.S0 s₀) j)[12] := by
    rw [← hcnt, ← h₃.st]
    simp [stateAt]
  have hm : s₈.mem = s₃.mem.writeW (VG.Proof.ChaCha20.X86.Xor.st s₀ + BitVec.ofNat 64 48) ((ctr (VG.Proof.ChaCha20.X86.Xor.S0 s₀) j)[12] + 4) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.gpr, u₅.mem, u₄.gpr, u₄.mem, e48, hv]
  have fW : Frame [VG.Proof.ChaCha20.X86.Xor.stR s₀] s₃.mem s₈.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (VG.Proof.ChaCha20.X86.Xor.contains_ofNat (by decide) (by decide))
  have hf : Frame (VG.Proof.ChaCha20.X86.Xor.qR s₀ j) s.mem s₈.mem := (h₃.frame.mono (by simp)).trans (fW.mono (by simp))
  refine ⟨⟨by rw [hg _ (by decide) (by decide) (by decide), h.ebx], ?_,
    by rw [hg _ (by decide) (by decide) (by decide), h.edi], ?_,
    by rw [hg _ (by decide) (by decide) (by decide), h.esp],
    by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, h₃.rd, h.rd],
    by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, h₃.wr, h.wr], fun _ => ?_, fun k hk => ?_,
    h.saved.frame hf (VG.Proof.ChaCha20.X86.Xor.qR_saved hp j), h.frame.trans (hf.sub (VG.Proof.ChaCha20.X86.Xor.qR_frame s₀ j))⟩, fW⟩
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      h₃.keep _ (by decide), h.esi, show (256 : BitVec 32) = BitVec.ofNat 32 256 from rfl, Offset.add_add, hP4]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      h₃.keep _ (by decide), h.ebp, show (256 : BitVec 32) = BitVec.ofNat 32 256 from rfl,
      Wp.sub_ofNat (by omega), hP4, Nat.sub_sub]
  · rw [hm, VG.Proof.ChaCha20.X86.Xor.stateAt_writeW_counter, h₃.st, hcnt, show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Proof.ChaCha20.X86.Xor.ctr_add]
  · -- The data.
    have e₁ : s₈.mem (VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 k) = s₃.mem (VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 k) :=
      fW.bytes (R := VG.Proof.ChaCha20.X86.Xor.dR s₀) (by simpa using hp.st_d.symm) (show VG.Proof.ChaCha20.X86.Xor.L s₀ ≤ 2 ^ 64 by omega) hk
    rw [e₁]
    by_cases hw : VG.Proof.ChaCha20.X86.Xor.P s₀ j ≤ k ∧ k < VG.Proof.ChaCha20.X86.Xor.P s₀ j + 256
    · have ea : VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 k = VG.Proof.ChaCha20.X86.Xor.win s₀ j + BitVec.ofNat 64 (k - VG.Proof.ChaCha20.X86.Xor.P s₀ j) := by
        rw [Offset.add_add, Nat.add_sub_cancel' hw.1]
      rw [ea, h₃.data _ (by omega), ite_eq_left (by simp only [Quad.Full]; omega), ← ea, h.data k hk,
        ite_eq_right (by omega), ite_eq_left (by omega : k < P s₀ (j + 4)), hcnt,
        VG.Proof.ChaCha20.X86.Xor.ksb_eq hPj (by omega), Nat.add_sub_cancel' hw.1]
    · rw [h₃.outside hp hk (by omega), h.data k hk]
      by_cases hk' : k < VG.Proof.ChaCha20.X86.Xor.P s₀ j
      · rw [ite_eq_left hk', ite_eq_left (by omega)]
      · rw [ite_eq_right hk', ite_eq_right (by omega)]

/-- At most 256 bytes left: the bytes after the last multiple of 16 XORed
with the keystream in `buf[0, 16)`, and no bytes left. -/
theorem last_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.X86.Xor.P s₀ j + 65 ≤ VG.Proof.ChaCha20.X86.Xor.L s₀) (hle : VG.Proof.ChaCha20.X86.Xor.L s₀ ≤ VG.Proof.ChaCha20.X86.Xor.P s₀ j + 256)
    {s s₃ : State} (h : VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s) (h₃ : VG.Proof.ChaCha20.X86.Xor.Q4 s₀ j s s₃) :
    WP isa last s₃ fun s' => VG.Proof.ChaCha20.X86.Xor.OInv s₀ (j + 4) s' ∧ Frame [VG.Proof.ChaCha20.X86.Xor.dR s₀] s₃.mem s'.mem := by
  have hL := VG.Proof.ChaCha20.X86.Xor.L_lt s₀
  have hd := hp.d_fit
  have hb := hp.b_fit
  have hPj : VG.Proof.ChaCha20.X86.Xor.P s₀ j = 64 * j := by simp only [VG.Proof.ChaCha20.X86.Xor.P] at *; omega
  have hP4 : VG.Proof.ChaCha20.X86.Xor.P s₀ (j + 4) = VG.Proof.ChaCha20.X86.Xor.L s₀ := by simp only [VG.Proof.ChaCha20.X86.Xor.P] at *; omega
  have hW : VG.Proof.ChaCha20.X86.Xor.Wn s₀ j = VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ j := by simp only [VG.Proof.ChaCha20.X86.Xor.Wn]; omega
  have hcnt := h.cnt (by omega)
  generalize hn : VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ j = n at hW
  have hq : n / 16 * 16 ≤ n := Nat.div_mul_le_self n 16
  -- The pointers and the count.
  unfold last
  refine WP.seq (WP.mono (Q := fun s₉ : State =>
      VG.Proof.ChaCha20.X86.Bytes.BPre s₉ (VG.Proof.ChaCha20.X86.Xor.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Xor.P s₀ j + n / 16 * 16)) (VG.Proof.ChaCha20.X86.Xor.BP s₀) (n % 16) ∧
        (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .ebp → s₉.gpr r = s.gpr r) ∧
        s₉.gpr .ebp = 0 ∧ s₉.mem = s₃.mem ∧ s₉.rd = s₀.rd ∧ s₉.wr = s₀.wr)
    (Wp.wp_mov fun s₄ u₄ => Wp.wp_andi fun s₅ u₅ => Wp.wp_andi fun s₆ u₆ =>
      Wp.wp_add fun s₇ u₇ _ => Wp.wp_mov fun s₈ u₈ => Wp.wp_movi fun s₉ u₉ => WP.block_nil ?_)
    fun s₁₀ hb₁₀ => ?_)
  · have hebp : s₃.gpr .ebp = BitVec.ofNat 32 n := by rw [h₃.keep _ (by decide), h.ebp, hn]
    have hesi : s₃.gpr .esi = VG.Proof.ChaCha20.X86.Xor.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Xor.P s₀ j) := by rw [h₃.keep _ (by decide), h.esi]
    have g : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .ebp → s₉.gpr r = s.gpr r :=
      fun r h1 h2 h3 h4 h5 => by
        rw [u₉.other r h5, u₈.other r h3, u₇.other r h4, u₆.other r h5, u₅.other r h2, u₄.other r h2,
          h₃.keep r h1]
    have hrd : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, h₃.rd, h.rd]
    have hwr : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, h₃.wr, h.wr]
    have hm : s₉.mem = s₃.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, fun k hk => ?_, fun k hk => ?_, fun a ha b hb' he => ?_⟩, g, u₉.gpr, hm, hrd, hwr⟩
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₆.other .esi (by decide),
        u₅.other .esi (by decide), u₅.other .ebp (by decide), u₄.other .esi (by decide),
        u₄.other .ebp (by decide), hesi, hebp, VG.Proof.ChaCha20.X86.Bytes.and_m16, VG.Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by omega), BitVec.add_assoc,
        BitVec.ofNat_add_ofNat]
    · rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.other _ (by decide), u₄.other _ (by decide), h₃.keep _ (by decide), h.edi]
    · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
        u₅.gpr, u₄.gpr, hebp, VG.Proof.ChaCha20.X86.Bytes.and_15, VG.Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by omega)]
    · by_cases hz : n % 16 = 0
      · rw [hz]; exact Nat.le_of_lt (BitVec.isLt _)
      · rw [VG.Proof.ChaCha20.X86.Bytes.ofNat32_add_toNat _ (by omega)]; omega
    · omega
    · rw [hwr, VG.Proof.ChaCha20.X86.Bytes.setWidth_add _ (by omega), Offset.add_add]
      exact ⟨VG.Proof.ChaCha20.X86.Xor.dR s₀, by simp [hp.wr], VG.Proof.ChaCha20.X86.Xor.contains_ofNat (by omega) (by lit_omega)⟩
    · rw [hrd, hwr]
      exact ⟨VG.Proof.ChaCha20.X86.Xor.bR s₀, by simp [hp.wr], VG.Proof.ChaCha20.X86.Xor.contains_ofNat (by omega) (by lit_omega)⟩
    · rw [VG.Proof.ChaCha20.X86.Bytes.setWidth_add _ (by omega), Offset.add_add] at he
      exact hp.d_b _ (VG.Proof.ChaCha20.X86.Xor.contains_ofNat (show VG.Proof.ChaCha20.X86.Xor.P s₀ j + n / 16 * 16 + a + 1 ≤ VG.Proof.ChaCha20.X86.Xor.L s₀ by omega) (by lit_omega))
        (by rw [he]; exact VG.Proof.ChaCha20.X86.Xor.contains_ofNat (show b + 1 ≤ 320 by omega) (by lit_omega))
  -- The bytes.
  obtain ⟨hb₁, g₁, hebp₁, hm₁, hrd₁, hwr₁⟩ := hb₁₀
  refine WP.mono (VG.Proof.ChaCha20.X86.Bytes.xorBytes_ok hb₁) fun s' h' => ?_
  have hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → r ≠ .ebp → s'.gpr r = s.gpr r :=
    fun r a b c d e => by rw [h'.keep r a b c d, g₁ r a b c d e]
  have hf' : Frame [VG.Proof.ChaCha20.X86.Xor.dR s₀] s₁₀.mem s'.mem := h'.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨VG.Proof.ChaCha20.X86.Xor.dR s₀, List.mem_singleton_self _, ?_⟩
    by_cases hz : n % 16 = 0
    · rw [hz]; intro x hx; simp only [Region.Contains] at hx; omega
    · rw [VG.Proof.ChaCha20.X86.Bytes.setWidth_add _ (by omega)]
      exact Offset.sub_base _ (by omega)
  have hf : Frame (VG.Proof.ChaCha20.X86.Xor.frameR s₀) s.mem s'.mem :=
    (h₃.frame.sub fun r hr => VG.Proof.ChaCha20.X86.Xor.qR_frame s₀ j r (by
      simp only [VG.Proof.ChaCha20.X86.Xor.qR, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp)).trans (hm₁ ▸ hf'.mono (by simp))
  refine ⟨⟨by rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide), h.ebx], ?_,
    by rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide), h.edi], ?_,
    by rw [hg _ (by decide) (by decide) (by decide) (by decide) (by decide), h.esp],
    by rw [h'.rd, hrd₁, hp.rd], by rw [h'.wr, hwr₁], fun hlt => absurd hlt (by omega), fun k hk => ?_,
    (h.saved.frame h₃.frame (fun r hr => VG.Proof.ChaCha20.X86.Xor.qR_saved hp j r (by
      simp only [VG.Proof.ChaCha20.X86.Xor.qR, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp))).frame (hm₁ ▸ hf') (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.d_b.symm.sub_left (VG.Proof.ChaCha20.X86.Xor.savR_sub s₀)),
    h.frame.trans hf⟩, by rw [← hm₁]; exact hf'⟩
  · rw [h'.esi, BitVec.add_assoc, BitVec.ofNat_add_ofNat, hP4]
    congr 2; omega
  · rw [h'.keep _ (by decide) (by decide) (by decide) (by decide), hebp₁, hP4, Nat.sub_self]; rfl
  · -- The data.
    rw [ite_eq_left (by omega)]
    have hD : ∀ i, i < n % 16 → ((VG.Proof.ChaCha20.X86.Xor.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Xor.P s₀ j + n / 16 * 16)).setWidth 64 + BitVec.ofNat 64 i) =
        VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86.Xor.P s₀ j + n / 16 * 16 + i) := fun i hi => by
      rw [VG.Proof.ChaCha20.X86.Bytes.setWidth_add _ (by omega), Offset.add_add]
    have hwin : ∀ t, VG.Proof.ChaCha20.X86.Xor.win s₀ j + BitVec.ofNat 64 t = VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 (VG.Proof.ChaCha20.X86.Xor.P s₀ j + t) :=
      fun t => Offset.add_add _ _ _
    have hout : ∀ k, k < VG.Proof.ChaCha20.X86.Xor.P s₀ j + n / 16 * 16 → s'.mem (VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 k) = s₁₀.mem (VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 k) :=
      fun k hk' => h'.frame _ fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [Region.Contains] at hcon
        have : 0 < n % 16 := by omega
        rw [VG.Proof.ChaCha20.X86.Bytes.setWidth_add _ (by omega), Offset.sub_toNat' _ (by lit_omega) (by lit_omega)] at hcon
        split at hcon <;> omega
    by_cases ha : k < VG.Proof.ChaCha20.X86.Xor.P s₀ j
    · rw [hout k (by omega), hm₁, h₃.outside hp hk (by omega), h.data k hk, ite_eq_left ha]
    by_cases hb' : k < VG.Proof.ChaCha20.X86.Xor.P s₀ j + n / 16 * 16
    · obtain ⟨t, rfl⟩ : ∃ t, k = VG.Proof.ChaCha20.X86.Xor.P s₀ j + t := ⟨k - VG.Proof.ChaCha20.X86.Xor.P s₀ j, by omega⟩
      rw [hout _ hb', hm₁, ← hwin, h₃.data t (by omega), ite_eq_left (by simp only [Quad.Full]; omega),
        hwin, h.data _ hk, ite_eq_right ha, hcnt, VG.Proof.ChaCha20.X86.Xor.ksb_eq hPj (by omega)]
    · obtain ⟨i, rfl⟩ : ∃ i, k = VG.Proof.ChaCha20.X86.Xor.P s₀ j + n / 16 * 16 + i := ⟨k - (VG.Proof.ChaCha20.X86.Xor.P s₀ j + n / 16 * 16), by omega⟩
      have h3 := h'.data i (by omega)
      rw [hD i (by omega)] at h3
      rw [h3, hm₁, show VG.Proof.ChaCha20.X86.Xor.P s₀ j + n / 16 * 16 + i = VG.Proof.ChaCha20.X86.Xor.P s₀ j + (n / 16 * 16 + i) by omega, ← hwin,
        h₃.data _ (by omega), ite_eq_right (by simp only [Quad.Full]; omega), hwin, h.data _ (by omega),
        ite_eq_right (by omega)]
      congr 1
      have hs := h₃.stash (by omega) trivial i (by omega)
      rw [hW, show Quad.sOff n = n / 16 * 16 from rfl] at hs
      rw [show VG.Proof.ChaCha20.X86.Xor.bp s₀ = (VG.Proof.ChaCha20.X86.Xor.BP s₀).setWidth 64 from rfl] at hs
      rw [hs, hcnt, VG.Proof.ChaCha20.X86.Xor.ksb_eq hPj (by omega)]

end Quad

theorem Q4.of {s₀ : State} {j : Nat} {s s₃ s₄ : State} (h : VG.Proof.ChaCha20.X86.Xor.Q4 s₀ j s s₃) (hg : s₄.gpr = s₃.gpr)
    (hm : s₄.mem = s₃.mem) (hr : s₄.rd = s₃.rd) (hw : s₄.wr = s₃.wr) : VG.Proof.ChaCha20.X86.Xor.Q4 s₀ j s s₄ :=
  ⟨fun k hk => by rw [hm]; exact h.data k hk, fun a b => by rw [hm]; exact h.stash a b,
    fun r hr' => by rw [hg]; exact h.keep r hr', by rw [hr, h.rd], by rw [hw, h.wr], hm ▸ h.frame,
    by rw [hm]; exact h.st⟩

theorem OInv.of {s₀ : State} {j : Nat} {s s' : State} (h : VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) : VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s' :=
  ⟨by rw [hg, h.ebx], by rw [hg, h.esi], by rw [hg, h.edi], by rw [hg, h.ebp], by rw [hg, h.esp],
    by rw [hr, h.rd], by rw [hw, h.wr], fun hl => by rw [hm]; exact h.cnt hl,
    fun k hk => by rw [hm, h.data k hk], by rw [hm]; exact h.saved, by rw [hm]; exact h.frame⟩

/-! ## Four blocks: the loop body -/

theorem body4_ok {k : Kernel} (Kk : Quad.KernelOk k) {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {j : Nat}
    (hj : VG.Proof.ChaCha20.X86.Xor.P s₀ j + 65 ≤ VG.Proof.ChaCha20.X86.Xor.L s₀) {s : State} (h : VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s) (hinv : Kk.Inv (VG.Proof.ChaCha20.X86.Xor.bp s₀) s.mem) :
    WP isa (body4 k) s fun s' => (VG.Proof.ChaCha20.X86.Xor.OInv s₀ (j + 4) s' ∧ Kk.Inv (VG.Proof.ChaCha20.X86.Xor.bp s₀) s'.mem) ∧
      s'.cf = some (decide (VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ (j + 4) < 65)) := by
  have hL := VG.Proof.ChaCha20.X86.Xor.L_lt s₀
  unfold body4
  refine VG.Proof.ChaCha20.X86.Xor.quad4_ok Kk hp hj h hinv fun s₃ h₃ => ?_
  have hinv₃ : Kk.Inv (VG.Proof.ChaCha20.X86.Xor.bp s₀) s₃.mem := Kk.inv_frame hinv h₃.frame fun r hr => VG.Proof.ChaCha20.X86.Xor.kR_qR hp j r (by
    simp only [VG.Proof.ChaCha20.X86.Xor.qR, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl <;> simp)
  refine WP.seq (WP.mono (Bytes.cmpi_ok s₃ .ebp 257) fun s₄ ⟨g₄, m₄, _, r₄, w₄, c₄⟩ => ?_)
  have hebp : s₃.gpr .ebp = BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ j) := by rw [h₃.keep _ (by decide), h.ebp]
  rw [hebp, VG.Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by omega), show (257 : BitVec 32).toNat = 257 from rfl] at c₄
  have h₄ := h₃.of g₄ m₄ r₄ w₄
  have hinv₄ : Kk.Inv (VG.Proof.ChaCha20.X86.Xor.bp s₀) s₄.mem := m₄ ▸ hinv₃
  refine WP.seq (WP.mono (Q := fun s₅ : State => VG.Proof.ChaCha20.X86.Xor.OInv s₀ (j + 4) s₅ ∧ Kk.Inv (VG.Proof.ChaCha20.X86.Xor.bp s₀) s₅.mem)
    (WP.ite (decide (VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ j < 257)) (by show eval .b s₄ = _; simp only [eval, c₄])
      (fun hlt => WP.mono (VG.Proof.ChaCha20.X86.Xor.last_ok hp hj (by simp only [decide_eq_true_eq] at hlt; omega) h h₄)
        fun s₅ ⟨h₅, f₅⟩ => ⟨h₅, Kk.inv_frame hinv₄ f₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hp.d_b.symm.sub_left (VG.Proof.ChaCha20.X86.Xor.kR_sub s₀))⟩)
      (fun hge => WP.mono (VG.Proof.ChaCha20.X86.Xor.next_ok hp (by simp only [decide_eq_false_iff_not] at hge; omega) h h₄)
        fun s₅ ⟨h₅, f₅⟩ => ⟨h₅, Kk.inv_frame hinv₄ f₅ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact hp.st_b.symm.sub_left (VG.Proof.ChaCha20.X86.Xor.kR_sub s₀))⟩))
    fun s₅ ⟨h₅, i₅⟩ => ?_)
  refine Wp.wp_cmpi fun s₆ u₆ hcf _ => WP.block_nil ⟨⟨h₅.of u₆.gpr u₆.mem u₆.rd u₆.wr, u₆.mem ▸ i₅⟩, ?_⟩
  rw [hcf, h₅.ebp, VG.Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by omega)]; rfl

/-! ## The last bytes -/

/-- What the epilogue needs: the data done, and our caller's registers saved. -/
structure Done (s₀ : State) (s : State) : Prop where
  edi : s.gpr .edi = VG.Proof.ChaCha20.X86.Xor.BP s₀
  esp : s.gpr .esp = VG.Proof.ChaCha20.X86.Xor.E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  data : ∀ k < VG.Proof.ChaCha20.X86.Xor.L s₀, s.mem (VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 k) = VG.Proof.ChaCha20.X86.Xor.D0 s₀ k ^^^ (VG.Proof.ChaCha20.X86.Xor.KS s₀).getD k 0
  saved : VG.Proof.ChaCha20.X86.Xor.Saved s₀ s.mem
  frame : Frame (VG.Proof.ChaCha20.X86.Xor.frameR s₀) s₀.mem s.mem

theorem OInv.done {s₀ : State} {j : Nat} {s : State} (h : VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s) (hj : VG.Proof.ChaCha20.X86.Xor.P s₀ j = VG.Proof.ChaCha20.X86.Xor.L s₀) : VG.Proof.ChaCha20.X86.Xor.Done s₀ s :=
  ⟨h.edi, h.esp, h.rd, h.wr, fun k hk => by rw [h.data k hk, ite_eq_left (by omega)], h.saved, h.frame⟩

theorem tail_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {j : Nat} (hj : VG.Proof.ChaCha20.X86.Xor.P s₀ j < VG.Proof.ChaCha20.X86.Xor.L s₀) (hle : VG.Proof.ChaCha20.X86.Xor.L s₀ ≤ VG.Proof.ChaCha20.X86.Xor.P s₀ j + 64)
    {s : State} (h : VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s) : WP isa tail s (VG.Proof.ChaCha20.X86.Xor.Done s₀) := by
  have hL := VG.Proof.ChaCha20.X86.Xor.L_lt s₀
  have hd := hp.d_fit
  have hb := hp.b_fit
  have hPj : VG.Proof.ChaCha20.X86.Xor.P s₀ j = 64 * j := by simp only [VG.Proof.ChaCha20.X86.Xor.P] at *; omega
  unfold tail
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Xor.call_ok hp hj h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := fun s₃ : State => VG.Proof.ChaCha20.X86.Bytes.WPre s₃ (VG.Proof.ChaCha20.X86.Xor.DP s₀ + BitVec.ofNat 32 (VG.Proof.ChaCha20.X86.Xor.P s₀ j)) (VG.Proof.ChaCha20.X86.Xor.BP s₀) (VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ j) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → s₃.gpr r = s₁.gpr r) ∧ s₃.mem = s₁.mem ∧
      s₃.rd = s₁.rd ∧ s₃.wr = s₁.wr)
    (Wp.wp_mov fun s₂ u₂ => Wp.wp_mov fun s₃ u₃ => WP.block_nil ?_) fun s₄ ⟨hw₄, g₄, m₄, r₄, w₄⟩ => ?_)
  · refine ⟨⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), h₁.esi],
      by rw [u₃.other _ (by decide), u₂.gpr, h₁.edi], by rw [u₃.gpr, u₂.other _ (by decide), h₁.ebp],
      by rw [VG.Proof.ChaCha20.X86.Bytes.ofNat32_add_toNat _ (by omega)] <;> omega, by omega, fun o n hn => ?_, fun o n hn => ?_, ?_⟩,
      fun r a b c d => by rw [u₃.other r b, u₂.other r c], by rw [u₃.mem, u₂.mem], by rw [u₃.rd, u₂.rd],
      by rw [u₃.wr, u₂.wr]⟩
    · rw [u₃.wr, u₂.wr, h₁.wr, VG.Proof.ChaCha20.X86.Bytes.setWidth_add _ (by omega), Offset.add_add]
      exact ⟨VG.Proof.ChaCha20.X86.Xor.dR s₀, by simp [hp.wr], VG.Proof.ChaCha20.X86.Xor.contains_ofNat (by omega) (by lit_omega)⟩
    · rw [u₃.rd, u₂.rd, u₃.wr, u₂.wr, h₁.rd, h₁.wr]
      exact ⟨VG.Proof.ChaCha20.X86.Xor.bR s₀, by simp [hp.wr], VG.Proof.ChaCha20.X86.Xor.contains_ofNat (by omega) (by lit_omega)⟩
    · rw [VG.Proof.ChaCha20.X86.Bytes.setWidth_add _ (by omega)]
      exact (hp.d_b.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by omega))
  refine WP.mono (VG.Proof.ChaCha20.X86.Bytes.xorWide_ok hw₄) fun s' h' => ?_
  have hf' : Frame [VG.Proof.ChaCha20.X86.Xor.dR s₀] s₄.mem s'.mem := h'.frame.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨VG.Proof.ChaCha20.X86.Xor.dR s₀, List.mem_singleton_self _, ?_⟩
    rw [VG.Proof.ChaCha20.X86.Bytes.setWidth_add _ (by omega)]
    exact Offset.sub_base _ (by omega)
  have hg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .esi → s'.gpr r = s₁.gpr r :=
    fun r a b c d => by rw [h'.keep r a b c d, g₄ r a b c d]
  refine ⟨by rw [hg _ (by decide) (by decide) (by decide) (by decide), h₁.edi],
    by rw [hg _ (by decide) (by decide) (by decide) (by decide), h₁.esp],
    by rw [h'.rd, r₄, h₁.rd], by rw [h'.wr, w₄, h₁.wr], fun k hk => ?_,
    h₁.saved.frame (m₄ ▸ hf') (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.d_b.symm.sub_left (VG.Proof.ChaCha20.X86.Xor.savR_sub s₀)),
    h₁.frame.trans (m₄ ▸ hf'.mono (by simp))⟩
  by_cases ha : k < VG.Proof.ChaCha20.X86.Xor.P s₀ j
  · have e : s'.mem (VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 k) = s₄.mem (VG.Proof.ChaCha20.X86.Xor.dp s₀ + BitVec.ofNat 64 k) := by
      refine h'.frame _ fun r hr hcon => ?_
      simp only [List.mem_singleton] at hr; subst hr
      simp only [Region.Contains] at hcon
      rw [VG.Proof.ChaCha20.X86.Bytes.setWidth_add _ (by omega), Offset.sub_toNat' _ (by lit_omega) (by lit_omega)] at hcon
      split at hcon <;> omega
    rw [e, m₄, h₁.data k hk, ite_eq_left ha]
  · obtain ⟨t, rfl⟩ : ∃ t, k = VG.Proof.ChaCha20.X86.Xor.P s₀ j + t := ⟨k - VG.Proof.ChaCha20.X86.Xor.P s₀ j, by omega⟩
    have h3 := h'.data t (by omega)
    rw [VG.Proof.ChaCha20.X86.Bytes.setWidth_add _ (by omega), Offset.add_add] at h3
    rw [h3, m₄, h₁.data _ hk, ite_eq_right ha]
    congr 1
    rw [h₁.ks t (by omega), VG.Proof.ChaCha20.X86.Xor.KS, keystream_getD _ hk, hPj, show (64 * j + t) / 64 = j by omega,
      show (64 * j + t) % 64 = t by omega]

/-! ## The epilogue -/

theorem restore_eq : restore = Spill.restoreCode .eax saved ++ [] := rfl

theorem ret_stack (s₀ : State) : (VG.Proof.ChaCha20.X86.Xor.retR s₀).Disjoint (VG.Proof.ChaCha20.X86.Xor.stackR s₀) := by
  have := Offset.disjoint_base (VG.Proof.ChaCha20.X86.Xor.Es s₀ - BitVec.ofNat 64 12) (d := 12) (n := 4) (k := 12) (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

set_option simprocs false in
theorem epilogue_ok {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {s : State} (h : VG.Proof.ChaCha20.X86.Xor.Done s₀ s) :
    WP isa (.block (.mov .eax (.reg .edi) :: restore)) s fun s' =>
      (abiPreserved s₀ s' ∧ Proof.ChaCha20.xorX86.post s₀ s') ∧ s'.gpr .eax = VG.Proof.ChaCha20.X86.Xor.BP s₀ := by
  have e : ∀ p ∈ saved, addr (VG.Proof.ChaCha20.X86.Xor.BP s₀) p.2 = VG.Proof.ChaCha20.X86.Xor.bp s₀ + BitVec.ofNat 64 p.2 :=
    fun p h => hp.eaB (by have := saved_fits.1 p h; lit_omega)
  rw [VG.Proof.ChaCha20.X86.Xor.restore_eq]
  refine Wp.wp_mov fun s₁ u₁ => ?_
  have hB : s₁.gpr .eax = VG.Proof.ChaCha20.X86.Xor.BP s₀ := by rw [u₁.gpr, h.edi]
  refine Spill.restore_ok saved (by decide) (fun p hp' => ?_)
    (by rw [hB, u₁.mem]; exact h.saved.congr (fun p h => (e p h).symm) fun _ _ => rfl)
    fun s' r' => WP.block_nil ⟨⟨⟨r'.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp]), ?_⟩, ?_⟩,
      by rw [r'.other _ (by decide), hB]⟩
  · have := saved_fits.1 p hp'
    rw [hB, u₁.rd, u₁.wr, e p hp']
    exact ⟨VG.Proof.ChaCha20.X86.Xor.bR s₀, by simp [h.rd, h.wr, hp.rd, hp.wr], VG.Proof.ChaCha20.X86.contains_off (by lit_omega) (by lit_omega)⟩
  · rw [r'.mem, u₁.mem]
    refine h.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.ret_st
    · exact hp.ret_d
    · exact hp.ret_b
    · exact VG.Proof.ChaCha20.X86.Xor.ret_stack s₀
  · show bytesAt s'.mem _ _ = _
    rw [r'.mem, u₁.mem]
    exact bytesAt_xor (length_keystream _ _) fun k hk => h.data k hk

/-! ## The whole function -/

theorem xor_eq (k : Kernel) : xorWith k =
    .seq (.block [.mov .eax (.mem (at_ .esp 16))]) (.seq (.block prologue) (.seq (.block k.init)
    (.seq (.block [.alu .cmp .ebp (.imm 65)])
    (.seq (.ite .b (.block []) (.loop (body4 k) .ae))
    (.seq (.block [.alu .test .ebp (.reg .ebp)])
    (.seq (.ite .e (.block []) tail) (.block (.mov .eax (.reg .edi) :: restore)))))))) := rfl

/-- The quarter round's constants stored in `buf[288, 320)`. -/
theorem init_ok {k : Kernel} (Kk : Quad.KernelOk k) {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {s : State}
    (h : VG.Proof.ChaCha20.X86.Xor.OInv s₀ 0 s) : WP isa (.block k.init) s fun s' => VG.Proof.ChaCha20.X86.Xor.OInv s₀ 0 s' ∧ Kk.Inv (VG.Proof.ChaCha20.X86.Xor.bp s₀) s'.mem := by
  have hL := VG.Proof.ChaCha20.X86.Xor.L_lt s₀
  have hc := VG.Proof.ChaCha20.X86.Xor.ctx_of hp h.ebx h.edi h.wr
  refine WP.mono (Kk.init_ok s hc.eaB hc.wb) fun s' ⟨hi, hf, hg, hr, hw⟩ => ⟨⟨by rw [hg _ (by decide), h.ebx],
    by rw [hg _ (by decide), h.esi], by rw [hg _ (by decide), h.edi], by rw [hg _ (by decide), h.ebp],
    by rw [hg _ (by decide), h.esp], by rw [hr, h.rd], by rw [hw, h.wr], fun hl => ?_, fun k hk => ?_,
    h.saved.frame hf (by simpa using (Offset.disjoint (VG.Proof.ChaCha20.X86.Xor.bp s₀) (d := 256) (n := 16) (e := 288) (k := 32)
      (by omega) (by decide) (by decide))),
    h.frame.trans (hf.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨VG.Proof.ChaCha20.X86.Xor.bR s₀, by simp, VG.Proof.ChaCha20.X86.Xor.kR_sub s₀⟩)⟩, hi⟩
  · rw [VG.Proof.ChaCha20.X86.Xor.stateAt_frame hf (by simpa using hp.st_b.sub_right (VG.Proof.ChaCha20.X86.Xor.kR_sub s₀)), h.cnt hl]
  · rw [hf.bytes (R := VG.Proof.ChaCha20.X86.Xor.dR s₀) (by simpa using hp.d_b.sub_right (VG.Proof.ChaCha20.X86.Xor.kR_sub s₀)) (show VG.Proof.ChaCha20.X86.Xor.L s₀ ≤ 2 ^ 64 by omega) hk,
      h.data k hk]

theorem cmp65_ok {s₀ : State} {s : State} (h : VG.Proof.ChaCha20.X86.Xor.OInv s₀ 0 s) {I : Mem → Prop} (hi : I s.mem) :
    WP isa (.block [.alu .cmp .ebp (.imm 65)]) s fun s' =>
      (VG.Proof.ChaCha20.X86.Xor.OInv s₀ 0 s' ∧ I s'.mem) ∧ s'.cf = some (decide (VG.Proof.ChaCha20.X86.Xor.L s₀ < 65)) := by
  have hL := VG.Proof.ChaCha20.X86.Xor.L_lt s₀
  refine Wp.wp_cmpi fun s' u hcf _ => WP.block_nil ⟨⟨h.of u.gpr u.mem u.rd u.wr, u.mem ▸ hi⟩, ?_⟩
  rw [hcf, h.ebp, VG.Proof.ChaCha20.X86.Bytes.toNat_ofNat_lt32 (by simp only [VG.Proof.ChaCha20.X86.Xor.P]; omega)]
  simp [VG.Proof.ChaCha20.X86.Xor.P]

theorem loop4_ok {k : Kernel} (Kk : Quad.KernelOk k) {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) {s : State}
    (h : VG.Proof.ChaCha20.X86.Xor.OInv s₀ 0 s) (hinv : Kk.Inv (VG.Proof.ChaCha20.X86.Xor.bp s₀) s.mem) (hL : 65 ≤ VG.Proof.ChaCha20.X86.Xor.L s₀) :
    WP isa (.loop (body4 k) .ae) s fun s' => ∃ j, VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ j < 65 ∧ VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s' := by
  let Inv : Nat → State → Prop := fun n s =>
    ∃ j, n = VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ j ∧ VG.Proof.ChaCha20.X86.Xor.P s₀ j + 65 ≤ VG.Proof.ChaCha20.X86.Xor.L s₀ ∧ VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s ∧ Kk.Inv (VG.Proof.ChaCha20.X86.Xor.bp s₀) s.mem
  have hstep : ∀ n s, Inv n s → WP isa (body4 k) s (fun s' =>
      (eval .ae s' = some false ∧ ∃ j, VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ j < 65 ∧ VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s') ∨
      (eval .ae s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨j, rfl, hj, hI, hi⟩
    refine WP.mono (VG.Proof.ChaCha20.X86.Xor.body4_ok Kk hp hj hI hi) fun s' ⟨⟨h', hi'⟩, hc'⟩ => ?_
    have hP : VG.Proof.ChaCha20.X86.Xor.P s₀ j < VG.Proof.ChaCha20.X86.Xor.P s₀ (j + 4) := by simp only [VG.Proof.ChaCha20.X86.Xor.P] at *; omega
    by_cases hl : VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ (j + 4) < 65
    · exact .inl ⟨by simp [eval, hc', hl], j + 4, hl, h'⟩
    · exact .inr ⟨by simp [eval, hc', hl], VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ (j + 4), by omega, j + 4, rfl, by omega, h', hi'⟩
  exact WP.loop (M := isa) Inv hstep (VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ 0) s ⟨0, rfl, by simp [VG.Proof.ChaCha20.X86.Xor.P]; omega, h, hinv⟩

theorem test_ok {s₀ : State} {j : Nat} {s : State} (h : VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s) :
    WP isa (.block [.alu .test .ebp (.reg .ebp)]) s fun s' =>
      VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s' ∧ s'.zf = some (decide (VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ j = 0)) := by
  have hL := VG.Proof.ChaCha20.X86.Xor.L_lt s₀
  refine Wp.wp_test fun s' u hz => WP.block_nil ⟨h.of u.gpr u.mem u.rd u.wr, ?_⟩
  rw [hz, h.ebp, BitVec.and_self, Wp.ofNat_beq_zero (by omega)]

theorem correct {k : Kernel} (Kk : Quad.KernelOk k) {s₀ : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s₀) :
    WP isa (xorWith k) s₀ fun s' =>
      (abiPreserved s₀ s' ∧ Proof.ChaCha20.xorX86.post s₀ s') ∧ s'.gpr .eax = VG.Proof.ChaCha20.X86.Xor.BP s₀ := by
  rw [VG.Proof.ChaCha20.X86.Xor.xor_eq]
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Xor.load_buf_ok hp) fun s e => ?_)
  subst e
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Xor.prologue_ok hp) fun s₀' h₀ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Xor.init_ok Kk hp h₀) fun s₀'' ⟨h₀', i₀⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Xor.cmp65_ok h₀' i₀) fun s₁ ⟨⟨h₁, i₁⟩, hc⟩ => ?_)
  refine WP.seq (WP.mono (Q := fun s => ∃ j, VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ j < 65 ∧ VG.Proof.ChaCha20.X86.Xor.OInv s₀ j s) ?_
    fun s₂ ⟨j, hj, h₂⟩ => ?_)
  · refine WP.ite (decide (VG.Proof.ChaCha20.X86.Xor.L s₀ < 65)) (by simp [eval, hc]) (fun h => ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      exact WP.block_nil (M := isa) ⟨0, by simp [VG.Proof.ChaCha20.X86.Xor.P]; omega, h₁⟩
    · simp only [decide_eq_false_iff_not] at h
      exact VG.Proof.ChaCha20.X86.Xor.loop4_ok Kk hp h₁ i₁ (by omega)
  refine WP.seq (WP.mono (VG.Proof.ChaCha20.X86.Xor.test_ok h₂) fun s₃ ⟨h₃, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.ChaCha20.X86.Xor.Done s₀) ?_ fun s₄ h₄ => VG.Proof.ChaCha20.X86.Xor.epilogue_ok hp h₄)
  have hle := VG.Proof.ChaCha20.X86.Xor.P_le s₀ j
  refine WP.ite (decide (VG.Proof.ChaCha20.X86.Xor.L s₀ - VG.Proof.ChaCha20.X86.Xor.P s₀ j = 0)) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · simp only [decide_eq_true_eq] at h
    exact WP.block_nil (M := isa) (h₃.done (by omega))
  · simp only [decide_eq_false_iff_not] at h
    exact VG.Proof.ChaCha20.X86.Xor.tail_ok hp (by omega) (by omega) h₃

/-- `vg_chacha20_xor` returns with `eax` holding `buf`, for a caller that
recomputes pointers from it. -/
theorem xor_eax (s : State) (hs : Proof.ChaCha20.xorX86.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86.Xor.xor s t s' ∧ abiPreserved s s' ∧
      (Proof.ChaCha20.xorX86.post s s' ∧ s'.gpr .eax = arg s 3) := by
  obtain ⟨t, s', he, ⟨h, hr⟩⟩ := VG.Proof.ChaCha20.X86.Xor.correct Kernels.sse2Ok (XPre.of s hs)
  exact ⟨t, s', he, h.1, h.2, hr⟩

/-- `vg_chacha20_xor_ssse3` returns with `eax` holding `buf`. -/
theorem xorSsse3_eax (s : State) (hs : Proof.ChaCha20.xorX86.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86.Xor.xorSsse3 s t s' ∧ abiPreserved s s' ∧
      (Proof.ChaCha20.xorX86.post s s' ∧ s'.gpr .eax = arg s 3) := by
  obtain ⟨t, s', he, ⟨h, hr⟩⟩ := VG.Proof.ChaCha20.X86.Xor.correct Kernels.ssse3Ok (XPre.of s hs)
  exact ⟨t, s', he, h.1, h.2, hr⟩

/-! ## Constant time

The taint analysis follows the frames and the calls into the block function.
On entry it knows `esp` and where the writable regions are: `state`, the data
(whose length varies), `buf` and the arguments, which are public and at
`esp + 4`, and whose words 0 and 3 are the base addresses of `state` and
`buf`; and that the 12 bytes below `esp` are free for the frames and the
return addresses of the calls. -/

def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [64, 0, 320, 16], bases := [(.esp, 3, 4)],
    slots := [(3, 0, 16)], wbases := [(3, 0, 0), (3, 12, 2)], room := 12 }

theorem setWidth_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

theorem argWord_eq {s : State} (hsp : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {k : Nat} (hk : k < 16) :
    addr (s.gpr .esp) 4 + BitVec.ofNat 64 k = argAddr s (k / 4) + BitVec.ofNat 64 (k % 4) := by
  simp only [argAddr]
  rw [show (s.gpr .esp + BitVec.ofNat 32 (4 + 4 * (k / 4))).setWidth 64 = addr (s.gpr .esp) (4 + 4 * (k / 4))
    from rfl, addr_eq (by lit_omega), addr_eq (by lit_omega), BitVec.add_assoc, BitVec.add_assoc,
    ← BitVec.ofNat_add, ← BitVec.ofNat_add]
  congr 2; omega

theorem wf₀ {s : State} (hp : VG.Proof.ChaCha20.X86.Xor.XPre s) : VG.X86.Taint.Wf VG.Proof.ChaCha20.X86.Xor.τ₀ s := by
  have hst := hp.st_fit; have hd := hp.d_fit; have hb := hp.b_fit
  have hs : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 := hp.sp_hi
  have hlo : 12 ≤ (s.gpr .esp).toNat := hp.sp_lo
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨?_, ?_, ?_⟩, ?_, ?_, fun h => absurd h (Nat.lt_irrefl 0),
    fun _ h => (List.not_mem_nil h).elim⟩ fun _ => ⟨hlo, ?_⟩
  · rw [hp.wr]
    exact .cons (Nat.le_refl _) (.cons (Nat.zero_le _) (.cons (Nat.le_refl _) (.cons (Nat.le_refl _) .nil)))
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_d, hp.st_b, hp.a_st.symm⟩, ⟨hp.d_b, hp.a_d.symm⟩, hp.a_b.symm, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · simp only [VG.Proof.ChaCha20.X86.Xor.st, VG.Proof.ChaCha20.X86.Xor.setWidth_toNat]; omega
    · simp only [VG.Proof.ChaCha20.X86.Xor.dp, VG.Proof.ChaCha20.X86.Xor.setWidth_toNat]; omega
    · simp only [VG.Proof.ChaCha20.X86.Xor.bp, VG.Proof.ChaCha20.X86.Xor.setWidth_toNat]; omega
    · show (addr (s.gpr .esp) 4).toNat + 16 ≤ 2 ^ 32
      rw [addr_eq (by lit_omega), BitVec.toNat_add, VG.Proof.ChaCha20.X86.Xor.setWidth_toNat, BitVec.toNat_ofNat]; omega
  · intro p hp'
    simp only [VG.Proof.ChaCha20.X86.Xor.τ₀, List.mem_singleton] at hp'
    subst hp'
    show addr (s.gpr .esp) 4 = (VG.X86.Taint.region s 3).base
    rw [VG.X86.Taint.region, hp.wr]; rfl
  · intro p hp'
    simp only [VG.Proof.ChaCha20.X86.Xor.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 0) 32) 0 = VG.Proof.ChaCha20.X86.Xor.st s
      simp [addr, VG.Proof.ChaCha20.X86.Xor.st, VG.Proof.ChaCha20.X86.Xor.ST, arg, argAddr]
    · refine ⟨by decide, ?_⟩
      simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp.wr]
      show addr (s.mem.readW (addr (s.gpr .esp) 4 + BitVec.ofNat 64 12) 32) 0 = VG.Proof.ChaCha20.X86.Xor.bp s
      rw [VG.Proof.ChaCha20.X86.Xor.argWord_eq hs (k := 12) (by lit_omega)]
      simp [addr, VG.Proof.ChaCha20.X86.Xor.bp, VG.Proof.ChaCha20.X86.Xor.BP, arg]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.stk_st
    · exact hp.stk_d
    · exact hp.stk_b
    · intro x h₁ h₂
      simp only [Region.Contains, VG.Proof.ChaCha20.X86.Xor.τ₀] at h₁ h₂
      rw [show argAddr s 0 = addr (s.gpr .esp) 4 from rfl, addr_eq (by lit_omega)] at h₂
      have := (s.gpr .esp).isLt
      have hE := VG.Proof.ChaCha20.X86.Xor.setWidth_toNat (s.gpr .esp)
      generalize (s.gpr .esp).setWidth 64 = E at *
      bv_omega

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.ChaCha20.xorX86.pre s₁) (h₂ : Proof.ChaCha20.xorX86.pre s₂)
    (hpub : Proof.ChaCha20.xorX86.pub s₁ s₂) : VG.X86.Taint.Agree VG.Proof.ChaCha20.X86.Xor.τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := XPre.of _ h₁; have hp₂ := XPre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.ChaCha20.X86.Xor.wf₀ hp₁, VG.Proof.ChaCha20.X86.Xor.wf₀ hp₂, ?_, ?_,
    fun h => absurd h (Nat.lt_irrefl 0), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  · simp only [VG.Proof.ChaCha20.X86.Xor.τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [VG.Proof.ChaCha20.X86.Xor.stR, VG.Proof.ChaCha20.X86.Xor.dR, VG.Proof.ChaCha20.X86.Xor.bR, VG.Proof.ChaCha20.X86.Xor.aR, VG.Proof.ChaCha20.X86.Xor.st, VG.Proof.ChaCha20.X86.Xor.dp, VG.Proof.ChaCha20.X86.Xor.bp, VG.Proof.ChaCha20.X86.Xor.L, VG.Proof.ChaCha20.X86.Xor.ST, VG.Proof.ChaCha20.X86.Xor.DP, VG.Proof.ChaCha20.X86.Xor.LN, VG.Proof.ChaCha20.X86.Xor.BP, argAddr, ha 0 (by lit_omega),
      ha 1 (by lit_omega), ha 2 (by lit_omega), ha 3 (by lit_omega), hesp]
  · intro sl hsl
    simp only [VG.Proof.ChaCha20.X86.Xor.τ₀, List.mem_singleton] at hsl
    subst hsl; decide
  · intro sl hsl k _ hk
    simp only [VG.Proof.ChaCha20.X86.Xor.τ₀, List.mem_singleton] at hsl
    subst hsl
    simp only [Nat.zero_add] at hk
    simp only [VG.X86.Taint.byteAddr, VG.X86.Taint.region, hp₁.wr, hp₂.wr]
    show s₁.mem (addr (s₁.gpr .esp) 4 + BitVec.ofNat 64 k) = s₂.mem (addr (s₂.gpr .esp) 4 + BitVec.ofNat 64 k)
    rw [VG.Proof.ChaCha20.X86.Xor.argWord_eq hp₁.sp_hi hk, VG.Proof.ChaCha20.X86.Xor.argWord_eq hp₂.sp_hi hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by lit_omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by lit_omega))]
    exact congrArg _ (ha _ (by lit_omega))

/-- Memory whose four argument slots (at `0x5004`) hold `0x1000`, `0x2000`,
`0` and `0x3000`. -/
def satMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5009 then 0x20 else if a = 0x5011 then 0x30 else 0

/-- A state satisfying the precondition (with no data). -/
def sat : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.ChaCha20.X86.Xor.satMem
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 0⟩, ⟨0x3000, 320⟩, ⟨0x5004, 16⟩]

theorem xor_correct (s : State) (hs : Proof.ChaCha20.xorX86.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86.Xor.xor s t s' ∧ abiPreserved s s' ∧
      Proof.ChaCha20.xorX86.post s s' :=
  (VG.Proof.ChaCha20.X86.Xor.xor_eax s hs).imp fun _ ⟨s', he, h, hp, _⟩ => ⟨s', he, h, hp⟩

theorem xorSsse3_correct (s : State) (hs : Proof.ChaCha20.xorX86.pre s) :
    ∃ t s', Exec isa Impl.ChaCha20.X86.Xor.xorSsse3 s t s' ∧ abiPreserved s s' ∧
      Proof.ChaCha20.xorX86.post s s' :=
  (VG.Proof.ChaCha20.X86.Xor.xorSsse3_eax s hs).imp fun _ ⟨s', he, h, hp, _⟩ => ⟨s', he, h, hp⟩

theorem xor_ct : ConstantTime isa Proof.ChaCha20.xorX86.pre Proof.ChaCha20.xorX86.pub
    Impl.ChaCha20.X86.Xor.xor :=
  VG.Taint.constantTime (A := sseTaint) VG.Proof.ChaCha20.X86.Xor.τ₀ (fun _ _ h₁ h₂ hp => VG.Proof.ChaCha20.X86.Xor.agree₀ h₁ h₂ hp) (by taint_decide)

theorem xorSsse3_ct : ConstantTime isa Proof.ChaCha20.xorX86.pre Proof.ChaCha20.xorX86.pub
    Impl.ChaCha20.X86.Xor.xorSsse3 :=
  VG.Taint.constantTime (A := sseTaint) VG.Proof.ChaCha20.X86.Xor.τ₀ (fun _ _ h₁ h₂ hp => VG.Proof.ChaCha20.X86.Xor.agree₀ h₁ h₂ hp) (by taint_decide)

theorem xorX86_implies : Proof.ChaCha20.xorX86.Implies (Spec.ChaCha20.xorContract X86.abi 12) := by
  have a0 : arg VG.Proof.ChaCha20.X86.Xor.sat 0 = 0x1000 := by decide
  have a1 : arg VG.Proof.ChaCha20.X86.Xor.sat 1 = 0x2000 := by decide
  have a2 : arg VG.Proof.ChaCha20.X86.Xor.sat 2 = 0 := by decide
  have a3 : arg VG.Proof.ChaCha20.X86.Xor.sat 3 = 0x3000 := by decide
  have e : argAddr VG.Proof.ChaCha20.X86.Xor.sat 0 = 0x5004 := by decide
  have esp : sat.gpr .esp = 0x5000 := rfl
  sig_implies [Spec.ChaCha20.xorContract, Spec.ChaCha20.xorSig, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes, Proof.ChaCha20.xorX86] [a0, a1, a2, a3, e, esp] using VG.Proof.ChaCha20.X86.Xor.sat

theorem xor_verified :
    Verified X86.target Impl.ChaCha20.X86.Xor.xor (Spec.ChaCha20.xorContract X86.abi 12) :=
  Verified.of_correct VG.Proof.ChaCha20.X86.Xor.xor_correct VG.Proof.ChaCha20.X86.Xor.xor_ct VG.Proof.ChaCha20.X86.Xor.xorX86_implies

theorem xorSsse3_verified :
    Verified X86.target Impl.ChaCha20.X86.Xor.xorSsse3 (Spec.ChaCha20.xorContract X86.abi 12) :=
  Verified.of_correct VG.Proof.ChaCha20.X86.Xor.xorSsse3_correct VG.Proof.ChaCha20.X86.Xor.xorSsse3_ct VG.Proof.ChaCha20.X86.Xor.xorX86_implies

end VG.Proof.ChaCha20.X86.Xor

end
