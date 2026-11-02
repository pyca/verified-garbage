module

public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec

/-!
# RSASSA-PKCS1-v1_5 on RISC-V: one instruction at a time

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaPkcs1Sig/PPC64LE/Wp.lean`), over the rules of
`Proof/Framework/RISCV64/Steps.lean`: an instruction that writes a register
`d` leaves a state `Only [d]`-related to the one before (every other
register, memory, the permissions and the stack pointer as they were) with
the value it wrote, and a store leaves one `MemTo` its memory. A run of them
composes into `Only rs` or, with stores, `Kept rs` (memory aside).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Sig.RISCV64

open VG VG.RISCV64
open VG.RISCV64.Steps (Upd Mupd)

/-- `s'` is `s` but for the registers `rs`. -/
structure Only (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- `s'` is `s` but for the registers `rs` and memory. -/
structure Kept (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- `s'` is `s` with memory `m`. -/
structure MemTo (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

namespace Only

theorem refl (rs : List Reg) (s : State) : Only rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Only rs s₁ s₂) (h₂ : Only rs' s₂ s₃) :
    Only (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1],
   h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem mono {rs rs' : List Reg} {s s' : State} (h : Only rs s s') (hs : ∀ r ∈ rs, r ∈ rs' := by decide) :
    Only rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.sp⟩

/-- A register not in `rs` is kept. -/
theorem get {rs : List Reg} {s s' : State} (h : Only rs s s') (r : Reg) (hr : r ∉ rs := by decide) :
    s'.gpr r = s.gpr r := h.gpr r hr

theorem keep {rs : List Reg} {s s' : State} (h : Only rs s s') : Kept rs s s' := ⟨h.gpr, h.rd, h.wr, h.sp⟩

end Only

namespace Kept

theorem refl (rs : List Reg) (s : State) : Kept rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Kept rs s₁ s₂) (h₂ : Kept rs' s₂ s₃) :
    Kept (rs ++ rs') s₁ s₃ :=
  ⟨fun r hr => by
    rw [List.mem_append, not_or] at hr
    rw [h₂.gpr r hr.2, h₁.gpr r hr.1],
   h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp⟩

theorem mono {rs rs' : List Reg} {s s' : State} (h : Kept rs s s') (hs : ∀ r ∈ rs, r ∈ rs' := by decide) :
    Kept rs' s s' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hs r h'), h.rd, h.wr, h.sp⟩

theorem get {rs : List Reg} {s s' : State} (h : Kept rs s s') (r : Reg) (hr : r ∉ rs := by decide) :
    s'.gpr r = s.gpr r := h.gpr r hr

end Kept

theorem MemTo.keep {s s' : State} {m : Mem} (h : MemTo s s' m) : Kept [] s s' :=
  ⟨fun r _ => by rw [h.gpr], h.rd, h.wr, h.sp⟩

theorem only_of_upd {s s' : State} {d : Reg} {v : BitVec 64} (u : Upd s s' d v) : Only [d] s s' :=
  ⟨fun r hr => u.other r (by simpa using hr), u.mem, u.rd, u.wr, u.sp⟩

theorem memTo_of_mupd {s s' : State} {m : Mem} (u : Mupd s s' m) : MemTo s s' m :=
  ⟨u.gpr, u.mem, u.rd, u.wr, u.sp⟩

theorem wp_nil {s : State} {Q : State → Prop} (h : Q s) : WP isa (.block []) s Q := WP.block_nil h

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_li {d : Reg} {imm : Nat} (h : imm < 2048)
    (k : ∀ s', Only [d] s s' → s'.gpr d = BitVec.ofNat 64 imm → WP isa (.block is) s' Q) :
    WP isa (.block (.li d (imm : Int) :: is)) s Q :=
  Steps.wp_li h fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_addi {d n : Reg} {imm : Nat}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n + BitVec.ofNat 64 imm → WP isa (.block is) s' Q)
    (h : imm < 2048 := by decide) :
    WP isa (.block (.addi d n (imm : Int) :: is)) s Q :=
  Steps.wp_addi h fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_subi {d n : Reg} {imm : Nat}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n - BitVec.ofNat 64 imm → WP isa (.block is) s' Q)
    (h : imm ≤ 2048 := by decide) :
    WP isa (.block (.addi d n (-(imm : Int)) :: is)) s Q :=
  Steps.wp_subi h fun s' u => k s' (only_of_upd u) u.gpr

/-- `mv d, n` (`addi d, n, 0`). -/
theorem wp_mov {d n : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n 0 :: is)) s Q :=
  Steps.wp_mv fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_add {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n + s.gpr m → WP isa (.block is) s' Q) :
    WP isa (.block (.add d n m :: is)) s Q :=
  Steps.wp_add fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_sub {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n - s.gpr m → WP isa (.block is) s' Q) :
    WP isa (.block (.sub d n m :: is)) s Q :=
  Steps.wp_sub fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_and {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  Steps.WP.cons exec_logic (k _ (only_of_upd (Upd.write _ _ _)) (Upd.write _ _ _).gpr)

theorem wp_or {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  Steps.wp_or fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_xor {d n m : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  Steps.wp_xor fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_srl {d n : Reg} {sh : Nat}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n >>> sh → WP isa (.block is) s' Q) (h : sh < 64 := by decide) :
    WP isa (.block (.shift .srl .d d n sh :: is)) s Q :=
  Steps.wp_srl h fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_sll {d n : Reg} {sh : Nat}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr n <<< sh → WP isa (.block is) s' Q) (h : sh < 64 := by decide) :
    WP isa (.block (.shift .sll .d d n sh :: is)) s Q :=
  Steps.wp_sll h fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_addSp {d : Reg} {imm : Nat}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.sp + BitVec.ofNat 64 imm → WP isa (.block is) s' Q)
    (h : imm < 2048 := by decide) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  Steps.wp_addSp h fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_lbu {t n : Reg} {off : Nat} {a : Addr}
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Only [t] s s' → s'.gpr t = (s.mem a).setWidth 64 → WP isa (.block is) s' Q)
    (ho : off < 2048 := by decide) :
    WP isa (.block (.load .b t n off :: is)) s Q :=
  Steps.wp_lbu ho ha hin fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_ld {t n : Reg} {off : Nat} {a : Addr}
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hal : a.toNat % 8 = 0) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Only [t] s s' → s'.gpr t = s.mem.readW a 64 → WP isa (.block is) s' Q)
    (ho : off < 2048 := by decide) :
    WP isa (.block (.load .d t n off :: is)) s Q :=
  Steps.wp_ld ho ha hal hin fun s' u => k s' (only_of_upd u) u.gpr

theorem wp_sb {t n : Reg} {off : Nat} {a : Addr}
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', MemTo s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q)
    (ho : off < 2048 := by decide) :
    WP isa (.block (.store .b t n off :: is)) s Q :=
  Steps.wp_sb ho ha hout fun s' u => k s' (memTo_of_mupd u)

theorem wp_sd {t n : Reg} {off : Nat} {a : Addr}
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hal : a.toNat % 8 = 0) (hout : InRegions s.wr a 8)
    (k : ∀ s', MemTo s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q)
    (ho : off < 2048 := by decide) :
    WP isa (.block (.store .d t n off :: is)) s Q :=
  Steps.wp_sd ho ha hal hout fun s' u => k s' (memTo_of_mupd u)

end

theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero r) s = some (s.gpr r != 0) := rfl

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero r) s = some (s.gpr r == 0) := rfl

theorem ne_zero_iff {x : BitVec 64} : (x != 0) = decide (x.toNat ≠ 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · intro h h0; exact h (BitVec.eq_of_toNat_eq (by simpa using h0))
  · intro h h0; exact h (by rw [h0]; rfl)

theorem ite_both {c : Cond} {th el : Prog isa} {s : State} {Q : State → Prop} (b : Bool)
    (hc : isa.eval c s = some b) (h₁ : WP isa th s Q) (h₂ : WP isa el s Q) : WP isa (.ite c th el) s Q := by
  cases b
  · exact WP.ite false hc (by simp) (fun _ => h₂)
  · exact WP.ite true hc (fun _ => h₁) (by simp)

end VG.Proof.RsaPkcs1Sig.RISCV64
