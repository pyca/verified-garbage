import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.MlKem.AArch64.Compress
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem.AArch64.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Impl.MlKem.AArch64.Ntt
import VerifiedGarbage.Proof.MlKem.KPke1024
import VerifiedGarbage.Impl.MlKem.AArch64.Encode

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.Wp`. -/
section

/-!
# ML-KEM on AArch64: one instruction at a time

Weakest-precondition rules for the instruction forms the ML-KEM code uses, in
continuation style: each rule runs one instruction in front of the rest of a
block, and hands the rest the state it leaves, with what changed (`Only`: only
the registers listed may differ; `MemTo`: only the memory differs). Values are
stated as natural numbers (`toNat`), which `omega` reasons about; the `_n`
lemmas turn the machine's operations into operations on them when nothing
wraps.
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64

/-! ## What an instruction changes -/

/-- `s'` is `s` but for the registers `rs`. -/
structure Only (rs : List Reg) (s s' : VG.AArch64.State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vcs : ∀ r ∈ VG.AArch64.preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

namespace Only

theorem refl (rs : List Reg) (s : VG.AArch64.State) : VG.Proof.MlKem.AArch64.Only rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem trans {rs rs' : List Reg} {s₁ s₂ s₃ : VG.AArch64.State} (h₁ : VG.Proof.MlKem.AArch64.Only rs s₁ s₂) (h₂ : VG.Proof.MlKem.AArch64.Only rs' s₂ s₃) :
    VG.Proof.MlKem.AArch64.Only (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1],
   h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, fun r hr => (h₂.vcs r hr).trans (h₁.vcs r hr)⟩

theorem mono {rs rs' : List Reg} {s s' : VG.AArch64.State} (h : VG.Proof.MlKem.AArch64.Only rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : VG.Proof.MlKem.AArch64.Only rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.sp, h.vcs⟩

/-- A register not in `rs` is kept. -/
theorem get {rs : List Reg} {s s' : VG.AArch64.State} (h : VG.Proof.MlKem.AArch64.Only rs s s') (r : Reg) (hr : r ∉ rs := by decide) :
    s'.gpr r = s.gpr r := h.gpr r hr

end Only

/-- `s'` is `s` with memory `m`. -/
structure MemTo (s s' : VG.AArch64.State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vcs : ∀ r ∈ VG.AArch64.preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

/-- `s'` is `s` but for the registers `rs` and the memory. -/
structure Keep (rs : List Reg) (s s' : VG.AArch64.State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vcs : ∀ r ∈ VG.AArch64.preservedV, (s'.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64

namespace Keep

theorem refl (rs : List Reg) (s : VG.AArch64.State) : VG.Proof.MlKem.AArch64.Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem trans {rs rs' : List Reg} {s₁ s₂ s₃ : VG.AArch64.State} (h₁ : VG.Proof.MlKem.AArch64.Keep rs s₁ s₂) (h₂ : VG.Proof.MlKem.AArch64.Keep rs' s₂ s₃) :
    VG.Proof.MlKem.AArch64.Keep (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1],
   h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp, fun r hr => (h₂.vcs r hr).trans (h₁.vcs r hr)⟩

theorem mono {rs rs' : List Reg} {s s' : VG.AArch64.State} (h : VG.Proof.MlKem.AArch64.Keep rs s s')
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : VG.Proof.MlKem.AArch64.Keep rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp, h.vcs⟩

theorem get {rs : List Reg} {s s' : VG.AArch64.State} (h : VG.Proof.MlKem.AArch64.Keep rs s s') (r : Reg) (hr : r ∉ rs := by decide) :
    s'.gpr r = s.gpr r := h.gpr r hr

end Keep

theorem Only.keep {rs : List Reg} {s s' : VG.AArch64.State} (h : VG.Proof.MlKem.AArch64.Only rs s s') : VG.Proof.MlKem.AArch64.Keep rs s s' :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.vcs⟩

theorem MemTo.keep {s s' : VG.AArch64.State} {m : Mem} (h : VG.Proof.MlKem.AArch64.MemTo s s' m) : VG.Proof.MlKem.AArch64.Keep [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp, h.vcs⟩

theorem write_x_gpr (s : VG.AArch64.State) (d : Reg) (v : BitVec 64) :
    (s.write .x d v).gpr d = v := by simp [State.write]

theorem only_write (s : VG.AArch64.State) (sz : Size) (d : Reg) (v : BitVec sz.bits) :
    VG.Proof.MlKem.AArch64.Only [d] s (s.write sz d v) :=
  ⟨fun r h => by simp only [List.mem_singleton] at h; simp [State.write, h], rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem WP.cons {i : Instr} {is : List Instr} {s s' : VG.AArch64.State} {Q : VG.AArch64.State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

theorem wp_nil {s : VG.AArch64.State} {Q : VG.AArch64.State → Prop} (h : Q s) : WP isa (.block []) s Q := WP.block_nil h

theorem read_one (m : Mem) (a : Addr) : (m.read a 1 : BitVec 8) = m a := by
  simp only [Mem.read]
  ext i hi
  rw [BitVec.getElem_append]
  simp only [show i < 8 by omega, dite_true]

/-! ## The instructions -/

section
variable {is : List Instr} {s : VG.AArch64.State} {Q : VG.AArch64.State → Prop}

theorem wp_x {i : Instr} {d : Reg} {v : BitVec 64} (he : exec i s = some (s.write .x d v))
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' → s'.gpr d = v → WP isa (.block is) s' Q) :
    WP isa (.block (i :: is)) s Q :=
  WP.cons he (k _ (VG.Proof.MlKem.AArch64.only_write _ _ _ _) (VG.Proof.MlKem.AArch64.write_x_gpr _ _ _))

theorem wp_add {d n m : Reg}
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' → s'.gpr d = s.gpr n + s.gpr m → WP isa (.block is) s' Q) :
    WP isa (.block (.add .x d n m :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp [exec, State.read]) k

theorem wp_sub {d n m : Reg}
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' → s'.gpr d = s.gpr n - s.gpr m → WP isa (.block is) s' Q) :
    WP isa (.block (.sub .x d n m :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp [exec, State.read]) k

theorem wp_addImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' → s'.gpr d = s.gpr n + BitVec.ofNat 64 imm → WP isa (.block is) s' Q) :
    WP isa (.block (.addImm .x d n imm :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp [exec, h, State.read]) k

theorem wp_mov {d n : Reg}
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' → s'.gpr d = s.gpr n → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.MlKem.AArch64.mov d n :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s' h e => k s' h (by rw [e]; exact BitVec.add_zero _)

theorem wp_subImm {d n : Reg} {imm : Nat} (h : imm < 4096)
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' → s'.gpr d = s.gpr n - BitVec.ofNat 64 imm → WP isa (.block is) s' Q) :
    WP isa (.block (.subImm .x d n imm :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp [exec, h, State.read]) k

theorem wp_and {d n m : Reg}
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' → s'.gpr d = (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and .x d n m :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp [exec, State.read]) k

theorem wp_orr {d n m : Reg}
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' → s'.gpr d = (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .orr .x d n m :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp [exec, State.read]) k

theorem wp_eor {d n m : Reg}
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' → s'.gpr d = (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp [exec, State.read]) k

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' → s'.gpr d = s.gpr n >>> sh → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .x d n sh :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp [exec, h, State.read]) k

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' → s'.gpr d = s.gpr n <<< sh → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl .x d n sh :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp [exec, h, State.read]) k

theorem wp_mul {d n m : Reg}
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' → s'.gpr d = s.gpr n * s.gpr m → WP isa (.block is) s' Q) :
    WP isa (.block (.mul .x d n m :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp [exec, State.read]) k

theorem wp_madd {d n m a : Reg}
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' → s'.gpr d = s.gpr a + s.gpr n * s.gpr m → WP isa (.block is) s' Q) :
    WP isa (.block (.madd .x d n m a :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp [exec, State.read]) k

theorem wp_movz {d : Reg} {imm : BitVec 16}
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' → s'.gpr d = imm.setWidth 64 → WP isa (.block is) s' Q) :
    WP isa (.block (.movz .x d imm 0 :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp [exec]) k

theorem wp_movk1 {d : Reg} {imm : BitVec 16}
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' →
      s'.gpr d = (s.gpr d &&& ~~~((0xFFFF : BitVec 64) <<< 16) ||| imm.setWidth 64 <<< 16) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.movk .x d imm 1 :: is)) s Q :=
  VG.Proof.MlKem.AArch64.wp_x (by simp only [exec, State.read, Size.bits, BitVec.setWidth_eq]; rfl) k

theorem wp_ldrw {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 4096 * 4)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [t] s s' → s'.gpr t = (s.mem.readW a 32).setWidth 64 → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .w t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .w t (s.mem.readW a 32)) ?_
    (k _ (VG.Proof.MlKem.AArch64.only_write _ _ _ _) (by simp [State.write]))
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
    Option.map_some, Mem.readW]
  try rfl

theorem wp_strw {t n : Reg} {off : Nat} {a : Addr} (ho : off % 4 = 0 ∧ off < 4096 * 4)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', VG.Proof.MlKem.AArch64.MemTo s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .w t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

theorem wp_ldrx {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [t] s s' → s'.gpr t = s.mem.readW a 64 → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr .x t n off :: is)) s Q := by
  refine WP.cons (s' := s.write .x t (s.mem.readW a 64)) ?_
    (k _ (VG.Proof.MlKem.AArch64.only_write _ _ _ _) (VG.Proof.MlKem.AArch64.write_x_gpr _ _ _))
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.load, hin,
    Option.map_some, Mem.readW]
  try rfl

theorem wp_strx {t n : Reg} {off : Nat} {a : Addr} (ho : off % 8 = 0 ∧ off < 4096 * 8)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', VG.Proof.MlKem.AArch64.MemTo s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str .x t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩)
  simp only [exec, addr, Size.bytes, ho, and_self, ite_true, ha, Option.bind_some, State.store, hout,
    Mem.writeW, State.read]
  try rfl

theorem wp_ldrb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [t] s s' → s'.gpr t = (s.mem a).setWidth 64 → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrb t n off :: is)) s Q := by
  have e : ((s.mem a).setWidth 32 : BitVec 32).setWidth 64 = (s.mem a).setWidth 64 := by
    ext i hi; simp
  refine WP.cons (s' := s.write .w t (((s.mem a).setWidth 32))) ?_ (k _ (VG.Proof.MlKem.AArch64.only_write _ _ _ _) ?_)
  · simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
      Option.bind_some, State.load, hin, Option.map_some, VG.Proof.MlKem.AArch64.read_one]
  · simp only [State.write, ite_true]
    exact e

theorem wp_strb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', VG.Proof.MlKem.AArch64.MemTo s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.strb t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩)
  simp only [exec, addr, Nat.mod_one, true_and, show off < 4096 * 1 by omega, ite_true, ha,
    Option.bind_some, State.store, hout, Mem.writeW, State.read]
  congr 3
  ext i hi; simp [Size.bits]; try omega

end

/-! ## Constants -/

/-- `movImm d v`: `d ← v`. -/
theorem wp_movImm {d : Reg} {v : BitVec 64} {is : List Instr} {s : VG.AArch64.State} {Q : VG.AArch64.State → Prop}
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d] s s' → s'.gpr d = v → WP isa (.block is) s' Q) :
    WP isa (.block (Impl.MlKem.AArch64.movImm d v ++ is)) s Q := by
  refine WP.cons rfl (WP.cons rfl (WP.cons rfl (WP.cons rfl (k _ ?_ ?_))))
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    simp only [List.mem_singleton] at hr
    simp [State.write, hr]
  · simp only [State.write, State.read, Size.bits, BitVec.setWidth_eq, ite_true]
    exact movz_movk64' v

/-! ## Branch conditions -/

theorem eval_zero (s : VG.AArch64.State) (r : Reg) : isa.eval (.zero .x r) s = some (s.gpr r == 0) := by
  simp [eval, State.read]

theorem eval_nonzero (s : VG.AArch64.State) (r : Reg) : isa.eval (.nonzero .x r) s = some (s.gpr r != 0) := by
  simp [eval, State.read]

theorem ne_zero_iff (x : BitVec 64) : (x != 0) = decide (x.toNat ≠ 0) := by
  have e : x = 0 ↔ x.toNat = 0 :=
    ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq (by simpa using h)⟩
  by_cases h : x.toNat = 0
  · have : x = 0 := e.mpr h
    subst this; rfl
  · have : x ≠ 0 := fun h' => h (e.mp h')
    simpa [h] using this

theorem eq_zero_iff (x : BitVec 64) : (x == 0) = decide (x.toNat = 0) := by
  rw [← Bool.not_not (x == 0), show (!(x == 0)) = (x != 0) from rfl, VG.Proof.MlKem.AArch64.ne_zero_iff]
  simp

/-- A do-while loop on `cbnz cr` that runs its body `n > 0` times: the
register is not zero exactly until the last iteration. -/
theorem count_loop {body : Prog isa} {cr : Reg} {n : Nat} (hn : 0 < n) (I : Nat → VG.AArch64.State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ ((s'.gpr cr).toNat ≠ 0 ↔ k + 1 ≠ n))
    {s : VG.AArch64.State} (h0 : I 0 s) : WP isa (.loop body (.nonzero .x cr)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hc⟩ => ?_
  have hz : isa.eval (.nonzero .x cr) s' = some (decide (k + 1 ≠ n)) := by
    rw [VG.Proof.MlKem.AArch64.eval_nonzero, VG.Proof.MlKem.AArch64.ne_zero_iff]
    exact congrArg some (decide_eq_decide.mpr hc)
  by_cases hl : k + 1 = n
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [hl] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## Numbers -/

theorem toNat_add_n {a b : BitVec 64} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem toNat_sub_n {a b : BitVec 64} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat := by
  rw [BitVec.toNat_sub]
  have := a.isLt
  omega

theorem toNat_mul_n {a b : BitVec 64} (h : a.toNat * b.toNat < 2 ^ 64) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem toNat_madd_n {a b c : BitVec 64} (h : a.toNat + b.toNat * c.toNat < 2 ^ 64) :
    (a + b * c).toNat = a.toNat + b.toNat * c.toNat := by
  rw [BitVec.toNat_add, BitVec.toNat_mul, Nat.add_mod_mod, Nat.mod_eq_of_lt h]

theorem toNat_lsr (a : BitVec 64) (n : Nat) : (a >>> n).toNat = a.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_lsl_n {a : BitVec 64} {n : Nat} (h : a.toNat * 2 ^ n < 2 ^ 64) :
    (a <<< n).toNat = a.toNat * 2 ^ n := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

theorem toNat_and_mask (a b : BitVec 64) {k : Nat} (h : b.toNat = 2 ^ k - 1) :
    (a &&& b).toNat = a.toNat % 2 ^ k := by
  rw [BitVec.toNat_and, h, Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_imm (imm : BitVec 16) : (imm.setWidth 64).toNat = imm.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := imm.isLt; omega)]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem toNat_readW32 (m : Mem) (a : Addr) : ((m.readW a 32).setWidth 64).toNat = (m.readW a 32).toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := (m.readW a 32).isLt; omega)]

theorem toNat_byte (b : Byte) : (b.setWidth 64).toNat = b.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]

/-- The low 32 bits of a register holding a number less than `2³²`. -/
theorem setWidth32_of_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) :
    x.setWidth 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat]

/-- The low byte of a register. -/
theorem setWidth8_of_toNat {x : BitVec 64} {n : Nat} (h : x.toNat = n) :
    x.setWidth 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat]

/-! ## Addresses -/

theorem ptr_next (p : Addr) (k c : Nat) :
    p + BitVec.ofNat 64 (c * k) + BitVec.ofNat 64 c = p + BitVec.ofNat 64 (c * (k + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]

theorem ptr_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem ptr_zero (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero _

/-- `[p + off, p + off + n)` is within the region `⟨p, len⟩` if `off + n ≤ len < 2⁶⁴`. -/
theorem contains_off {p : Addr} {off n len : Nat} (h : off + n ≤ len) (hl : len < 2 ^ 64) :
    (⟨p, len⟩ : Region).Contains (p + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show p + BitVec.ofNat 64 off - p = BitVec.ofNat 64 off by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem in_regions {rs : List Region} {R : Region} (hR : R ∈ rs) {a : Addr} {n : Nat}
    (h : R.Contains a n) : InRegions rs a n := ⟨R, hR, h⟩

theorem in_rd_wr {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨R, hR, hc⟩ := h
  exact ⟨R, List.mem_append_right _ hR, hc⟩

theorem in_rd {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions rd a n) :
    InRegions (rd ++ wr) a n := by
  obtain ⟨R, hR, hc⟩ := h
  exact ⟨R, List.mem_append_left _ hR, hc⟩

/-- Bytes `[a, a + n)` and `[b, b + k)` at offsets of one base, apart. -/
theorem sep_off (p : Addr) {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n < 2 ^ 64)
    (hb : b + k < 2 ^ 64) : Mem.Sep (p + BitVec.ofNat 64 a) n (p + BitVec.ofNat 64 b) k := by
  intro x h₁ h₂
  have e : ∀ c, c < 2 ^ 64 → (x - (p + BitVec.ofNat 64 c)).toNat = ((x - p).toNat + 2 ^ 64 - c) % 2 ^ 64 := by
    intro c hc
    rw [show x - (p + BitVec.ofNat 64 c) = (x - p) - BitVec.ofNat 64 c by bv_omega, BitVec.toNat_sub,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
    omega
  rw [e a (by omega)] at h₁
  rw [e b (by omega)] at h₂
  have := (x - p).isLt
  omega

end VG.Proof.MlKem.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.Reduce`. -/
section

/-!
# ML-KEM on AArch64: reductions modulo `q`

The conditional subtraction `csub` (`Impl/MlKem/AArch64/Basic.lean`), for any
registers.
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem (q)
open VG.Proof.MlKem (condSub q_eq)

theorem not_mem_one {a b : Reg} (h : a ≠ b) : a ∉ [b] := by simpa using h

theorem not_mem_two {a b c : Reg} (h₁ : a ≠ b) (h₂ : a ≠ c) : a ∉ [b, c] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h₁, h₂⟩

/-- The arithmetic of `csub`: for `x < 2q`, `x - q`, plus `q` if it is
negative, is `x mod q`. -/
theorem csub_arith {x : Nat} (hx : x < 2 * q) :
    ((BitVec.ofNat 64 x - BitVec.ofNat 64 q) +
      ((BitVec.ofNat 64 x - BitVec.ofNat 64 q) >>> 63) * BitVec.ofNat 64 q).toNat = condSub x := by
  rw [q_eq] at hx
  rw [BitVec.toNat_add, BitVec.toNat_mul, VG.Proof.MlKem.AArch64.toNat_lsr, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat, condSub, q_eq]
  split <;> omega

/-- `csub d t qr`: `d ← d mod q` for `d < 2q`. -/
theorem csub_ok {d t qr : Reg} (hdt : d ≠ t) (hdq : d ≠ qr) (htq : t ≠ qr)
    {is : List Instr} {s : State} {Q : State → Prop} {x : Nat}
    (hx : x < 2 * q) (hd : (s.gpr d).toNat = x) (hq : (s.gpr qr).toNat = q)
    (k : ∀ s', VG.Proof.MlKem.AArch64.Only [d, t] s s' → (s'.gpr d).toNat = condSub x → WP isa (.block is) s' Q) :
    WP isa (.block (csub d t qr ++ is)) s Q := by
  refine VG.Proof.MlKem.AArch64.wp_sub fun s₁ h₁ e₁ => VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun s₂ h₂ e₂ => VG.Proof.MlKem.AArch64.wp_madd fun s₃ h₃ e₃ => ?_
  refine k s₃ (((h₁.trans h₂).trans h₃).mono (by simp)) ?_
  have hd' : s.gpr d = BitVec.ofNat 64 x := by
    rw [← hd, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hq' : s.gpr qr = BitVec.ofNat 64 q := by
    rw [← hq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have q₂ : s₂.gpr qr = s.gpr qr := by
    rw [h₂.get qr (VG.Proof.MlKem.AArch64.not_mem_one htq.symm), h₁.get qr (VG.Proof.MlKem.AArch64.not_mem_one hdq.symm)]
  have d₂ : s₂.gpr d = s₁.gpr d := h₂.get d (VG.Proof.MlKem.AArch64.not_mem_one hdt)
  rw [e₃, d₂, e₂, q₂, e₁, hd', hq']
  exact VG.Proof.MlKem.AArch64.csub_arith hx

end VG.Proof.MlKem.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.Common`. -/
section

/-!
# ML-KEM on AArch64: what the proofs share

Memory of zeros (for the states that show a precondition satisfiable), the
tactic that moves a proof from a per-target contract to the shared one, and
facts about the registers a function never writes.
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64
open VG.Spec.MlKem

theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0) p i = 0 := by
  simp only [coeffAt, Mem.readW, Mem.read]
  rfl

/-- A polynomial of zeros is reduced. -/
theorem reduced_zero (p : Addr) : Reduced (fun _ => 0) p := fun i _ => by
  rw [VG.Proof.MlKem.AArch64.coeffAt_zero]; decide

/-- `k.Implies k'` for `k'` built with `Sig.contract`, as `sig_implies`
proves it, where the satisfying state `w` may have preconditions on
polynomials of zeros (`reduced_zero`). -/
syntax "mlkem_implies " "[" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " using " term : tactic
macro_rules
  | `(tactic| mlkem_implies [$ls,*] [$ws,*] using $w) => `(tactic| exact
      { pre := by sig_implies_pre [$ls,*]
        post := by sig_implies_post [$ls,*]
        pub := by sig_implies_pub [$ls,*]
        sat := by
          refine ⟨$w, ?_⟩
          sig_pre [$ls,*]
          and_intros
          all_goals first
            | rfl
            | decide
            | exact Region.disjoint_of_sep (by decide)
            | exact reduced_zero _ _ ‹_›
            | exact reduced_zero _
            | (intro a h₁ h₂
               set_option linter.unusedSimpArgs false in
               simp only [Region.Contains, $ws,*] at h₁ h₂
               bv_omega) })

/-- No instruction of `c` (without calls) writes a callee-saved register. -/
theorem preserved_of {c : Prog isa} (h : c.allInstrs (keeps (RegSet.ofList preserved)) = true) :
    ∀ r ∈ preserved, ∀ i ∈ instrs c, dstOf i ≠ some r := by
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp (instrs_keeps h) i hi) r hr
  simpa using this

/-- Code without calls that writes no callee-saved register, and keeps the
stack pointer, meets the calling convention. -/
theorem abi_of {c : Prog isa} (hc : c.noCalls = true)
    (h : c.allInstrs (keeps (RegSet.ofList preserved)) = true) {s s' : State} {t : List Leak}
    (he : Exec isa c s t s') (hv : c.allInstrs keepsV = true := by decide +kernel) : abiPreserved s s' :=
  ⟨fun r hr => Exec.gpr (VG.Proof.MlKem.AArch64.preserved_of h r hr) he (.inl hc), Exec.sp he, Exec.preservedV he hv⟩

/-- Agreement on the registers `rs` and the stack pointer. -/
theorem agree_of {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (VG.AArch64.Taint.mem_ofRegs.mp hr)⟩

/-! ## Outputs written in order -/

theorem addr_ne (p : Addr) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    p + BitVec.ofNat 64 a ≠ p + BitVec.ofNat 64 b := by
  intro e
  apply h
  bv_omega

/-- Byte `j` after writing byte `c` of the bytes at `p`. -/
theorem write8_at (m : Mem) (p : Addr) {j c : Nat} (hj : j < 2 ^ 64) (hc : c < 2 ^ 64) (b : Byte) :
    m.writeW (p + BitVec.ofNat 64 c) b (p + BitVec.ofNat 64 j) =
      if j = c then b else m (p + BitVec.ofNat 64 j) := by
  rw [VG.WriteBytes.writeW8_apply]
  by_cases h : j = c
  · subst h; simp
  · rw [ite_eq_right (VG.Proof.MlKem.AArch64.addr_ne p hj hc h), ite_eq_right h]

/-- The bytes at `p`: the first `t` of them are `L`'s, the others `old`'s. -/
def BytesUpTo (m : Mem) (p : Addr) (N t : Nat) (L old : Nat → Byte) : Prop :=
  ∀ j < N, m (p + BitVec.ofNat 64 j) = if j < t then L j else old j

theorem BytesUpTo.zero {m : Mem} {p : Addr} {N : Nat} (L : Nat → Byte) :
    VG.Proof.MlKem.AArch64.BytesUpTo m p N 0 L fun j => m (p + BitVec.ofNat 64 j) := fun j _ => by
  rw [ite_eq_right (Nat.not_lt_zero j)]

/-- Writing byte `t`. -/
theorem BytesUpTo.write {m : Mem} {p : Addr} {N t : Nat} {L old : Nat → Byte}
    (h : VG.Proof.MlKem.AArch64.BytesUpTo m p N t L old) (hN : N < 2 ^ 64) (ht : t < N) {b : Byte} (hb : b = L t) :
    VG.Proof.MlKem.AArch64.BytesUpTo (m.writeW (p + BitVec.ofNat 64 t) b) p N (t + 1) L old := fun j hj => by
  rw [VG.Proof.MlKem.AArch64.write8_at m p (by omega) (by omega)]
  by_cases e : j = t
  · subst e; rw [ite_eq_left rfl, ite_eq_left (by omega), hb]
  · rw [ite_eq_right e, h j hj]
    by_cases hjt : j < t
    · rw [ite_eq_left hjt, ite_eq_left (by omega)]
    · rw [ite_eq_right hjt, ite_eq_right (by omega)]

/-- All `N` bytes written. -/
theorem BytesUpTo.eq {m : Mem} {p : Addr} {N : Nat} {L : Nat → Byte} {old : Nat → Byte}
    (h : VG.Proof.MlKem.AArch64.BytesUpTo m p N N L old) {xs : List Byte} (hl : xs.length = N)
    (hx : ∀ j < N, xs[j]! = L j) : Spec.Sha3.bytesAt m p N = xs :=
  bytesAt_eq! hl fun j hj => by rw [h j hj, ite_eq_left hj, hx j hj]

/-- The coefficients at `p`: the first `t` of them are `G`'s, the others `old`'s. -/
def CoeffsUpTo (m : Mem) (p : Addr) (t : Nat) (G old : Nat → BitVec 32) : Prop :=
  ∀ i < 256, coeffAt m p i = if i < t then G i else old i

theorem CoeffsUpTo.zero {m : Mem} {p : Addr} (G : Nat → BitVec 32) :
    VG.Proof.MlKem.AArch64.CoeffsUpTo m p 0 G fun i => coeffAt m p i := fun i _ => by
  rw [ite_eq_right (Nat.not_lt_zero i)]

/-- Writing coefficient `t`. -/
theorem CoeffsUpTo.write {m : Mem} {p : Addr} {t : Nat} {G old : Nat → BitVec 32}
    (h : VG.Proof.MlKem.AArch64.CoeffsUpTo m p t G old) (ht : t < 256) {v : BitVec 32} (hv : v = G t) :
    VG.Proof.MlKem.AArch64.CoeffsUpTo (m.writeW (coeffAddr p t) v) p (t + 1) G old := fun i hi => by
  rw [coeffAt_writeW m p (show i < n from hi) (show t < n from ht)]
  by_cases e : t = i
  · subst e; rw [ite_eq_left rfl, ite_eq_left (by omega), hv]
  · rw [ite_eq_right e, h i hi]
    by_cases hit : i < t
    · rw [ite_eq_left hit, ite_eq_left (by omega)]
    · rw [ite_eq_right hit, ite_eq_right (by omega)]

/-- All 256 coefficients written. -/
theorem CoeffsUpTo.polyIs {m : Mem} {p : Addr} {G old : Nat → BitVec 32}
    (h : VG.Proof.MlKem.AArch64.CoeffsUpTo m p 256 G old) {f : Poly} (hf : ∀ i < 256, G i = BitVec.ofNat 32 (f[i]!).val) :
    PolyIs m p f :=
  polyIs_of_coeffAt fun i hi => by rw [h i hi, ite_eq_left hi, hf i hi]

/-- A coefficient of a polynomial in a region the frame does not write. -/
theorem coeffAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) {i : Nat} (hi : i < 256) :
    coeffAt m' p i = coeffAt m p i :=
  coeffAt_congr (bytes_frame hf hd (by decide)) (show i < n from hi)

/-- A byte of a region the frame does not write. -/
theorem byte_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {len : Nat}
    (hd : ∀ r ∈ rs, (⟨p, len⟩ : Region).Disjoint r) (hlen : len ≤ 2 ^ 64) {j : Nat} (hj : j < len) :
    m' (p + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j) :=
  bytes_frame hf hd hlen j hj

end VG.Proof.MlKem.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.Barrett`. -/
section

/-!
# ML-KEM on AArch64: the tables

`table` stores a table of 128 `u32`s; the tables of the code are those of the
standard (`zetaTable_eq`, `gammaTable_eq`).
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem (q)

theorem zetaTable_eq : zetaTable = zetas := rfl

theorem gammaTable_eq : gammaTable = gammas := rfl

theorem zetaTable_lt : ∀ k < 128, zetaTable.getD k 0 < q := by decide +kernel

theorem gammaTable_lt : ∀ k < 128, gammaTable.getD k 0 < q := by decide +kernel

/-! ## Tables -/

/-- After the first `k` entries of a table. -/
structure TabInv (T : List Nat) (b : Reg) (s₀ : State) (k : Nat) (s : State) : Prop where
  keep : VG.Proof.MlKem.AArch64.Keep [.x9] s₀ s
  frame : Frame [⟨s₀.gpr b, 512⟩] s₀.mem s.mem
  tab : ∀ j < k, s.mem.readW (s₀.gpr b + BitVec.ofNat 64 (4 * j)) 32 = BitVec.ofNat 32 (T.getD j 0)

/-- `table T b` stores the table `T` at `b`. -/
theorem table_ok (T : List Nat) (hT : ∀ k < 128, T.getD k 0 < 65536) {b : Reg} (hb : b ≠ .x9)
    {s₀ : State} (hin : ∀ k < 128, InRegions s₀.wr (s₀.gpr b + BitVec.ofNat 64 (4 * k)) 4) :
    WP isa (.block (table T b)) s₀ (VG.Proof.MlKem.AArch64.TabInv T b s₀ 128) := by
  refine wp_range_flatMap (M := isa) (VG.Proof.MlKem.AArch64.TabInv T b s₀) (fun k s hk h => ?_) 128 (Nat.le_refl _) s₀
    ⟨Keep.refl _ _, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have hbk : s.gpr b = s₀.gpr b := h.keep.get b (VG.Proof.MlKem.AArch64.not_mem_one hb)
  refine VG.Proof.MlKem.AArch64.wp_movz fun s₁ h₁ e₁ => VG.Proof.MlKem.AArch64.wp_strw (a := s₀.gpr b + BitVec.ofNat 64 (4 * k))
    ⟨by omega, by omega⟩ (by rw [h₁.get b (VG.Proof.MlKem.AArch64.not_mem_one hb), hbk]) (by rw [h₁.wr, h.keep.wr]; exact hin k hk)
    fun s₂ h₂ => VG.Proof.MlKem.AArch64.wp_nil ?_
  have v : (s₁.gpr .x9).setWidth 32 = BitVec.ofNat 32 (T.getD k 0) := by
    refine VG.Proof.MlKem.AArch64.setWidth32_of_toNat ?_
    rw [e₁, VG.Proof.MlKem.AArch64.toNat_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hT k hk)]
  refine ⟨(h.keep.trans (h₁.keep.trans h₂.keep)).mono, ?_, fun j hj => ?_⟩
  · rw [h₂.mem, h₁.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (VG.Proof.MlKem.AArch64.contains_off (by omega) (by decide))
  · rw [h₂.mem, h₁.mem, v]
    by_cases e : j = k
    · subst e; exact Mem.readW_writeW_self32 _ _ _
    · rw [Mem.readW_writeW_sep (VG.Proof.MlKem.AArch64.sep_off _ (by omega) (by omega) (by omega)) (by decide)]
      exact h.tab j (by omega)

end VG.Proof.MlKem.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.AArch64.Cbd2`. -/
section

/-!
# ML-KEM on AArch64: `vg_mlkem_cbd2`

Two coefficients per byte (`samplePolyCBD2_val`): the sums of the pairs of
bits of a byte `v`, `s = (v & 0x55) + ((v >> 1) & 0x55)`, are `x` and `y` of
both nibbles (`sums`, checked for every byte by the kernel).
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- AArch64 contract for `vg_mlkem_cbd2(b = x0, f = x1)`: writes
`SamplePolyCBD₂` of the 128 bytes at `b` to `f`, reduced. The code may read
`b` and write `f`, which do not overlap. -/
def cbd2AArch64 : Contract AArch64.isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, 128⟩] ∧ s.wr = [⟨s.gpr .x1, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 128⟩ ⟨s.gpr .x1, 1024⟩
  post s s' := PolyIs s'.mem (s.gpr .x1) (samplePolyCBD 2 (bytesAt s.mem (s.gpr .x0) 128))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Cbd2

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The sums of pairs of bits of a byte. -/
def sums (v : Nat) : Nat := (v &&& 85) + (v / 2 &&& 85)

theorem sums_ok : ∀ v < 256, VG.Proof.MlKem.AArch64.Cbd2.sums v % 4 = cbdX v ∧ VG.Proof.MlKem.AArch64.Cbd2.sums v / 4 % 4 = cbdY v ∧
    VG.Proof.MlKem.AArch64.Cbd2.sums v / 16 % 4 = cbdX (v / 16) ∧ VG.Proof.MlKem.AArch64.Cbd2.sums v / 64 = cbdY (v / 16) ∧ VG.Proof.MlKem.AArch64.Cbd2.sums v < 256 := by
  decide +kernel

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .x0
abbrev fP : Addr := s₀.gpr .x1
abbrev bR : Region := ⟨VG.Proof.MlKem.AArch64.Cbd2.bP s₀, 128⟩
abbrev B : List Byte := bytesAt s₀.mem (VG.Proof.MlKem.AArch64.Cbd2.bP s₀) 128
/-- Coefficient `i` of the output. -/
def G (i : Nat) : BitVec 32 := BitVec.ofNat 32 ((samplePolyCBD 2 (VG.Proof.MlKem.AArch64.Cbd2.B s₀))[i]!).val
/-- Byte `j` of the input, as a number. -/
abbrev byte (j : Nat) : Nat := ((VG.Proof.MlKem.AArch64.Cbd2.B s₀).getD j 0).toNat

end

theorem G_even (s₀ : State) {k : Nat} (hk : k < 128) :
    VG.Proof.MlKem.AArch64.Cbd2.G s₀ (2 * k) = BitVec.ofNat 32 (condSub (VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) % 4 + q - VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) / 4 % 4)) := by
  have hv : VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k < 256 := byte_lt _
  have hq : q = 3329 := rfl
  obtain ⟨e1, e2, -, -, -⟩ := VG.Proof.MlKem.AArch64.Cbd2.sums_ok _ hv
  have := cbdX_le (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k)
  have := cbdY_le (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k)
  rw [VG.Proof.MlKem.AArch64.Cbd2.G, samplePolyCBD2_val _ (show 2 * k < n by rw [n_eq]; omega), e1, e2, condSub_eq (by omega)]
  refine congrArg (BitVec.ofNat 32) (congrArg (· % q) ?_)
  simp only [nibble, show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega, Nat.pow_zero,
    Nat.div_one]

theorem G_odd (s₀ : State) {k : Nat} (hk : k < 128) :
    VG.Proof.MlKem.AArch64.Cbd2.G s₀ (2 * k + 1) = BitVec.ofNat 32 (condSub (VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) / 16 % 4 + q - VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) / 64)) := by
  have hv : VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k < 256 := byte_lt _
  have hq : q = 3329 := rfl
  obtain ⟨-, -, e1, e2, -⟩ := VG.Proof.MlKem.AArch64.Cbd2.sums_ok _ hv
  have := cbdX_le (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k / 16)
  have := cbdY_le (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k / 16)
  rw [VG.Proof.MlKem.AArch64.Cbd2.G, samplePolyCBD2_val _ (show 2 * k + 1 < n by rw [n_eq]; omega), e1, e2, condSub_eq (by omega)]
  refine congrArg (BitVec.ofNat 32) (congrArg (· % q) ?_)
  simp only [nibble, show (2 * k + 1) / 2 = k by omega, show (2 * k + 1) % 2 = 1 by omega, Nat.pow_one]

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.MlKem.AArch64.Cbd2.bR s₀]
  wr : s₀.wr = [polyRegion (VG.Proof.MlKem.AArch64.Cbd2.fP s₀)]
  disj : (VG.Proof.MlKem.AArch64.Cbd2.bR s₀).Disjoint (polyRegion (VG.Proof.MlKem.AArch64.Cbd2.fP s₀))

/-- After `k` bytes. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = VG.Proof.MlKem.AArch64.Cbd2.bP s₀ + BitVec.ofNat 64 k
  x1 : s.gpr .x1 = VG.Proof.MlKem.AArch64.Cbd2.fP s₀ + BitVec.ofNat 64 (8 * k)
  x12 : (s.gpr .x12).toNat = q
  x14 : (s.gpr .x14).toNat = 85
  x15 : (s.gpr .x15).toNat = 3
  x16 : (s.gpr .x16).toNat = 128 - k
  out : VG.Proof.MlKem.AArch64.CoeffsUpTo s.mem (VG.Proof.MlKem.AArch64.Cbd2.fP s₀) (2 * k) (VG.Proof.MlKem.AArch64.Cbd2.G s₀) fun i => coeffAt s₀.mem (VG.Proof.MlKem.AArch64.Cbd2.fP s₀) i
  frame : Frame [polyRegion (VG.Proof.MlKem.AArch64.Cbd2.fP s₀)] s₀.mem s.mem

theorem Pre.byte_eq {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Cbd2.Pre s₀) {m : Mem} (hf : Frame [polyRegion (VG.Proof.MlKem.AArch64.Cbd2.fP s₀)] s₀.mem m)
    {j : Nat} (hj : j < 128) : (m (VG.Proof.MlKem.AArch64.Cbd2.bP s₀ + BitVec.ofNat 64 j)).toNat = VG.Proof.MlKem.AArch64.Cbd2.byte s₀ j := by
  rw [VG.Proof.MlKem.AArch64.byte_frame (len := 128) hf (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.disj)
    (by decide) hj]
  show _ = ((bytesAt s₀.mem (VG.Proof.MlKem.AArch64.Cbd2.bP s₀) 128).getD j 0).toNat
  rw [bytesAt_getD _ _ hj]

theorem step {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Cbd2.Pre s₀) {k : Nat} (hk : k < 128) {s : State} (h : VG.Proof.MlKem.AArch64.Cbd2.Inv s₀ k s) :
    WP isa (.block cbd2Body) s fun s' =>
      VG.Proof.MlKem.AArch64.Cbd2.Inv s₀ (k + 1) s' ∧ ((s'.gpr .x16).toNat ≠ 0 ↔ k + 1 ≠ 128) := by
  have hq : q = 3329 := rfl
  have hv : VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k < 256 := byte_lt _
  obtain ⟨-, -, -, -, hS⟩ := VG.Proof.MlKem.AArch64.Cbd2.sums_ok _ hv
  have c0 : s.gpr .x1 + BitVec.ofNat 64 0 = coeffAddr (VG.Proof.MlKem.AArch64.Cbd2.fP s₀) (2 * k) := by
    rw [h.x1, VG.Proof.MlKem.AArch64.ptr_zero, coeffAddr, show 4 * (2 * k) = 8 * k by omega]
  have c1 : s.gpr .x1 + BitVec.ofNat 64 4 = coeffAddr (VG.Proof.MlKem.AArch64.Cbd2.fP s₀) (2 * k + 1) := by
    rw [h.x1, VG.Proof.MlKem.AArch64.ptr_add, coeffAddr, show 8 * k + 4 = 4 * (2 * k + 1) by omega]
  have hout : ∀ i < 256, InRegions s.wr (coeffAddr (VG.Proof.MlKem.AArch64.Cbd2.fP s₀) i) 4 := fun i hi => by
    rw [h.wr, hp.wr]
    exact VG.Proof.MlKem.AArch64.in_regions (List.mem_singleton_self _) (coeff_contains _ (show i < n from hi))
  refine VG.Proof.MlKem.AArch64.wp_ldrb (a := VG.Proof.MlKem.AArch64.Cbd2.bP s₀ + BitVec.ofNat 64 k) (by decide) (by rw [h.x0, VG.Proof.MlKem.AArch64.ptr_zero]) ?_
    fun s₁ h₁ e₁ => ?_
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    exact VG.Proof.MlKem.AArch64.in_rd (VG.Proof.MlKem.AArch64.in_regions (List.mem_singleton_self _) (VG.Proof.MlKem.AArch64.contains_off (by omega) (by decide)))
  have v9 : (s₁.gpr .x9).toNat = VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k := by rw [e₁, VG.Proof.MlKem.AArch64.toNat_byte, hp.byte_eq h.frame hk]
  refine VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun s₂ h₂ e₂ => VG.Proof.MlKem.AArch64.wp_and fun s₃ h₃ e₃ => VG.Proof.MlKem.AArch64.wp_and fun s₄ h₄ e₄ =>
    VG.Proof.MlKem.AArch64.wp_add fun s₅ h₅ e₅ => ?_
  have k₅ := (((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep
  have a3 : (s₃.gpr .x9).toNat = VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k &&& 85 := by
    rw [e₃, BitVec.toNat_and, h₂.get .x9, v9]
    simp (disch := decide) only [h₂.gpr, h₁.gpr]
    rw [h.x14]
  have a4 : (s₄.gpr .x10).toNat = VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k / 2 &&& 85 := by
    rw [e₄, BitVec.toNat_and, h₃.get .x10, e₂, VG.Proof.MlKem.AArch64.toNat_lsr, v9]
    simp (disch := decide) only [h₃.gpr, h₂.gpr, h₁.gpr]
    rw [h.x14]
  have x9 : (s₅.gpr .x9).toNat = VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) := by
    have b3 := Nat.and_le_right (n := VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) (m := 85)
    have b4 := Nat.and_le_right (n := VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k / 2) (m := 85)
    rw [e₅, VG.Proof.MlKem.AArch64.toNat_add_n (by rw [h₄.get .x9, a3, a4]; omega), h₄.get .x9, a3, a4]
    rfl
  refine VG.Proof.MlKem.AArch64.wp_and fun s₆ h₆ e₆ => VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun s₇ h₇ e₇ => VG.Proof.MlKem.AArch64.wp_and fun s₈ h₈ e₈ =>
    VG.Proof.MlKem.AArch64.wp_add fun s₉ h₉ e₉ => VG.Proof.MlKem.AArch64.wp_sub fun s₁₀ h₁₀ e₁₀ => ?_
  have k₁₀ := ((((k₅.trans h₆.keep).trans h₇.keep).trans h₈.keep).trans h₉.keep).trans h₁₀.keep
  have x15 : ∀ {t : State}, t.gpr .x15 = s.gpr .x15 → (t.gpr .x15).toNat = 2 ^ 2 - 1 := fun e => by
    rw [e, h.x15]
  have x12 : ∀ {t : State}, t.gpr .x12 = s.gpr .x12 → (t.gpr .x12).toNat = q := fun e => by
    rw [e, h.x12]
  have v6 : (s₆.gpr .x10).toNat = VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) % 4 := by
    rw [e₆, VG.Proof.MlKem.AArch64.toNat_and_mask _ _ (x15 (k₅.get .x15)), x9]
  have v8 : (s₈.gpr .x11).toNat = VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) / 4 % 4 := by
    rw [e₈, VG.Proof.MlKem.AArch64.toNat_and_mask _ _ (x15 ((k₅.trans h₆.keep).trans h₇.keep |>.get .x15)), e₇, VG.Proof.MlKem.AArch64.toNat_lsr,
      h₆.get .x9, x9]
  have v9' : (s₉.gpr .x10).toNat = VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) % 4 + q := by
    rw [e₉, VG.Proof.MlKem.AArch64.toNat_add_n (by rw [h₈.get .x10, h₇.get .x10, v6, x12 (((k₅.trans h₆.keep).trans
                             h₇.keep).trans h₈.keep |>.get .x12)]; omega), h₈.get .x10, h₇.get .x10, v6,
      x12 (((k₅.trans h₆.keep).trans h₇.keep).trans h₈.keep |>.get .x12)]
  have v10 : (s₁₀.gpr .x10).toNat = VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) % 4 + q - VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) / 4 % 4 := by
    rw [e₁₀, VG.Proof.MlKem.AArch64.toNat_sub_n (by rw [v9', h₉.get .x11, v8]; omega), v9', h₉.get .x11, v8]
  refine VG.Proof.MlKem.AArch64.csub_ok (by decide) (by decide) (by decide) (by rw [hq]; omega) v10
    (x12 (k₁₀.get .x12)) fun s₁₁ h₁₁ e₁₁ => ?_
  have k₁₁ := k₁₀.trans h₁₁.keep
  refine VG.Proof.MlKem.AArch64.wp_strw (a := coeffAddr (VG.Proof.MlKem.AArch64.Cbd2.fP s₀) (2 * k)) (by decide) (by rw [k₁₁.get .x1]; exact c0)
    (by rw [k₁₁.wr]; exact hout _ (by omega)) fun s₁₂ h₁₂ => ?_
  refine VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun s₁₃ h₁₃ e₁₃ => VG.Proof.MlKem.AArch64.wp_and fun s₁₄ h₁₄ e₁₄ =>
    VG.Proof.MlKem.AArch64.wp_lsr (by decide) fun s₁₅ h₁₅ e₁₅ => VG.Proof.MlKem.AArch64.wp_add fun s₁₆ h₁₆ e₁₆ => VG.Proof.MlKem.AArch64.wp_sub fun s₁₇ h₁₇ e₁₇ => ?_
  have k₁₇ := ((((k₁₁.trans h₁₂.keep).trans h₁₃.keep).trans h₁₄.keep).trans h₁₅.keep).trans
    h₁₆.keep |>.trans h₁₇.keep
  have y9 : (s₁₂.gpr .x9).toNat = VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) := by
    rw [h₁₂.gpr, (((((h₆.keep.trans h₇.keep).trans h₈.keep).trans h₉.keep).trans h₁₀.keep).trans
      h₁₁.keep).get .x9, x9]
  have v14 : (s₁₄.gpr .x10).toNat = VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) / 16 % 4 := by
    rw [e₁₄, VG.Proof.MlKem.AArch64.toNat_and_mask _ _ (x15 ((k₁₁.trans h₁₂.keep).trans h₁₃.keep |>.get .x15)), e₁₃,
      VG.Proof.MlKem.AArch64.toNat_lsr, y9]
  have v15 : (s₁₅.gpr .x11).toNat = VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) / 64 := by
    rw [e₁₅, VG.Proof.MlKem.AArch64.toNat_lsr, h₁₄.get .x9, h₁₃.get .x9, y9]
  have v16 : (s₁₆.gpr .x10).toNat = VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) / 16 % 4 + q := by
    have e12 := x12 ((((k₁₁.trans h₁₂.keep).trans h₁₃.keep).trans h₁₄.keep).trans h₁₅.keep |>.get .x12)
    rw [e₁₆, VG.Proof.MlKem.AArch64.toNat_add_n (by rw [h₁₅.get .x10, v14, e12]; omega), h₁₅.get .x10, v14, e12]
  have v17 : (s₁₇.gpr .x10).toNat = VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) / 16 % 4 + q - VG.Proof.MlKem.AArch64.Cbd2.sums (VG.Proof.MlKem.AArch64.Cbd2.byte s₀ k) / 64 := by
    rw [e₁₇, VG.Proof.MlKem.AArch64.toNat_sub_n (by rw [v16, h₁₆.get .x11, v15]; omega), v16, h₁₆.get .x11, v15]
  refine VG.Proof.MlKem.AArch64.csub_ok (by decide) (by decide) (by decide) (by rw [hq]; omega) v17
    (x12 (k₁₇.get .x12)) fun s₁₈ h₁₈ e₁₈ => ?_
  have k₁₈ := k₁₇.trans h₁₈.keep
  refine VG.Proof.MlKem.AArch64.wp_strw (a := coeffAddr (VG.Proof.MlKem.AArch64.Cbd2.fP s₀) (2 * k + 1)) (by decide) (by rw [k₁₈.get .x1]; exact c1)
    (by rw [k₁₈.wr]; exact hout _ (by omega)) fun s₁₉ h₁₉ => ?_
  refine VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₂₀ h₂₀ e₂₀ => VG.Proof.MlKem.AArch64.wp_addImm (by decide) fun s₂₁ h₂₁ e₂₁ =>
    VG.Proof.MlKem.AArch64.wp_subImm (by decide) fun s₂₂ h₂₂ e₂₂ => VG.Proof.MlKem.AArch64.wp_nil ?_
  have k₁₉ := k₁₈.trans h₁₉.keep
  have k₂₁ := (k₁₉.trans h₂₀.keep).trans h₂₁.keep
  have k₂₂ := k₂₁.trans h₂₂.keep
  have m₂₂ : s₂₂.mem = (s.mem.writeW (coeffAddr (VG.Proof.MlKem.AArch64.Cbd2.fP s₀) (2 * k)) ((s₁₁.gpr .x10).setWidth 32)).writeW
      (coeffAddr (VG.Proof.MlKem.AArch64.Cbd2.fP s₀) (2 * k + 1)) ((s₁₈.gpr .x10).setWidth 32) := by
    rw [h₂₂.mem, h₂₁.mem, h₂₀.mem, h₁₉.mem, h₁₈.mem, h₁₇.mem, h₁₆.mem, h₁₅.mem, h₁₄.mem, h₁₃.mem,
      h₁₂.mem, h₁₁.mem, h₁₀.mem, h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem,
      h₁.mem]
  have c16 : (s₂₁.gpr .x16).toNat = 128 - k := by rw [k₂₁.get .x16, h.x16]
  have w16 : (s₂₂.gpr .x16).toNat = 128 - (k + 1) := by
    rw [e₂₂, VG.Proof.MlKem.AArch64.toNat_sub_n (by rw [c16]; simp; omega), c16]
    simp
    omega
  refine ⟨⟨by rw [k₂₂.rd, h.rd], by rw [k₂₂.wr, h.wr], by rw [k₂₂.sp, h.sp], ?_, ?_,
    by rw [k₂₂.get .x12, h.x12], by rw [k₂₂.get .x14, h.x14], by rw [k₂₂.get .x15, h.x15], w16, ?_,
    ?_⟩, by rw [w16]; omega⟩
  · rw [h₂₂.get .x0, h₂₁.get .x0, e₂₀, k₁₉.get .x0, h.x0, VG.Proof.MlKem.AArch64.ptr_add]
  · rw [h₂₂.get .x1, e₂₁, h₂₀.get .x1, k₁₉.get .x1, h.x1, VG.Proof.MlKem.AArch64.ptr_next]
  · rw [m₂₂, show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
    exact (h.out.write (by omega) (by rw [VG.Proof.MlKem.AArch64.setWidth32_of_toNat e₁₁, VG.Proof.MlKem.AArch64.Cbd2.G_even _ hk])).write (by omega)
      (by rw [VG.Proof.MlKem.AArch64.setWidth32_of_toNat e₁₈, VG.Proof.MlKem.AArch64.Cbd2.G_odd _ hk])
  · rw [m₂₂]
    exact (h.frame.writeW (List.mem_singleton_self _) _ (coeff_contains _ (show 2 * k < 256 by omega))).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (show 2 * k + 1 < 256 by omega))

theorem loop_ok {s₀ : State} (hp : VG.Proof.MlKem.AArch64.Cbd2.Pre s₀) : WP isa cbd2 s₀ (VG.Proof.MlKem.AArch64.Cbd2.Inv s₀ 128) := by
  refine WP.seq (VG.Proof.MlKem.AArch64.wp_movz fun s₁ h₁ e₁ => VG.Proof.MlKem.AArch64.wp_movz fun s₂ h₂ e₂ => VG.Proof.MlKem.AArch64.wp_movz fun s₃ h₃ e₃ =>
    VG.Proof.MlKem.AArch64.wp_movz fun s₄ h₄ e₄ => VG.Proof.MlKem.AArch64.wp_nil ?_)
  refine VG.Proof.MlKem.AArch64.count_loop (by decide) (VG.Proof.MlKem.AArch64.Cbd2.Inv s₀) (fun k hk s h => VG.Proof.MlKem.AArch64.Cbd2.step hp hk h) ?_
  have k₄ := ((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep
  have m₄ : s₄.mem = s₀.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨k₄.rd, k₄.wr, k₄.sp, by rw [k₄.get .x0, VG.Proof.MlKem.AArch64.ptr_zero],
    by rw [k₄.get .x1, Nat.mul_zero, VG.Proof.MlKem.AArch64.ptr_zero], by rw [h₄.get .x12, e₃, VG.Proof.MlKem.AArch64.toNat_imm]; rfl,
    by rw [h₄.get .x14, h₃.get .x14, h₂.get .x14, e₁, VG.Proof.MlKem.AArch64.toNat_imm]; rfl,
    by rw [h₄.get .x15, h₃.get .x15, e₂, VG.Proof.MlKem.AArch64.toNat_imm]; rfl, by rw [e₄, VG.Proof.MlKem.AArch64.toNat_imm]; rfl, ?_, ?_⟩
  · rw [m₄, Nat.mul_zero]; exact CoeffsUpTo.zero _
  · rw [m₄]; exact Frame.refl _ _

theorem correct (s : State) (hs : cbd2AArch64.pre s) :
    ∃ t s', Exec isa cbd2 s t s' ∧ abiPreserved s s' ∧ cbd2AArch64.post s s' := by
  obtain ⟨h1, h2, h3⟩ := hs
  obtain ⟨t, s', he, hI⟩ := VG.Proof.MlKem.AArch64.Cbd2.loop_ok (s₀ := s) ⟨h1, h2, h3⟩
  exact ⟨t, s', he, VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he,
    (show VG.Proof.MlKem.AArch64.CoeffsUpTo s'.mem (VG.Proof.MlKem.AArch64.Cbd2.fP s) 256 _ _ from hI.out).polyIs fun _ _ => rfl⟩

theorem ct : ConstantTime isa cbd2AArch64.pre cbd2AArch64.pub cbd2 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1])
    (fun _ _ _ _ ⟨h0, h1, hsp⟩ => VG.Proof.MlKem.AArch64.agree_of hsp (by simp [h0, h1])) (by taint_decide)

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x2000, 1024⟩]

theorem cbd2_verified : Verified AArch64.target cbd2 (Spec.MlKem.cbd2Contract AArch64.abi) :=
  Verified.of_correct VG.Proof.MlKem.AArch64.Cbd2.correct VG.Proof.MlKem.AArch64.Cbd2.ct (by
    mlkem_implies [Spec.MlKem.cbd2Contract, Spec.MlKem.cbd2Sig, VG.Proof.MlKem.cbd2AArch64, AArch64.abi,
      AArch64.argRegs] [sat] using VG.Proof.MlKem.AArch64.Cbd2.sat)

end VG.Proof.MlKem.AArch64.Cbd2

end
