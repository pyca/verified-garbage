import VerifiedGarbage.Proof.Gcm.X86_64.Stitch.Aes
import VerifiedGarbage.Proof.Gcm.X86_64.StitchAvx8.Buffer

/-!
# The part of the eight-state loop preserved by its scratch preparation

The hash inputs and counter templates occupy bytes 512–767. The powers,
constants and saved entry registers lie outside that range. Keeping their
frame separate lets both integer preparation and AES rounds preserve them.
-/

namespace VG.Proof.Gcm.X86_64.StitchAvx8

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Stitch
open VG.Spec.Gcm (Block)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Proof.Gcm.X86_64 (revMask)

def workR (s₀ : State) : Region := ⟨pp s₀ + 512, 256⟩

/-- The memory and pointers that every complete batch preserves. -/
structure Env (s₀ : State) (P : Nat → Block) (s : State) : Prop where
  rdi : s.gpr .rdi = kp s₀
  rsi : s.gpr .rsi = cp s₀
  rcx : s.gpr .rcx = yp s₀
  r11 : s.gpr .r11 = pp s₀
  r10 : s.gpr .r10 = kp s₀ + BitVec.ofNat 64 (16 * nr s₀)
  other : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .rsi →
    s.gpr r = s₀.gpr r
  frame : Frame [dR s₀, pR s₀] s₀.mem s.mem
  powers : ∀ k < 8, s.mem.readW (pp s₀ + BitVec.ofNat 64 (128 + 16 * k)) 128 = P k
  mask : s.mem.readW (pp s₀ + 768) 128 = revMask
  poly : s.mem.readW (pp s₀ + 784) 128 = poly
  rounds : s.mem.readW (pp s₀ + 800) 64 = s₀.gpr .rsi
  data : s.mem.readW (pp s₀ + 808) 64 = dp s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Env.keys {s₀ s : State} {P : Nat → Block} (hp : SPre s₀) (h : Env s₀ P s) :
    VG.Proof.Aes.X86_64.AesNi.Keys (nr s₀) (sch s₀) s :=
  ⟨by rw [h.rdi, sch_frame hp h.frame], by rcases hp.rounds with h | h | h <;> omega,
    fun j hj => by
      rw [h.rd, h.wr, h.rdi]
      exact in_sub_int hp.k_in (by rcases hp.rounds with h | h | h <;> omega)⟩

theorem Env.yframe {s₀ s t : State} {P : Nat → Block} {rs : List XReg}
    (h : Env s₀ P s) (f : YFrame rs s t) : Env s₀ P t := by
  constructor
  · rw [f.gpr]; exact h.rdi
  · rw [f.gpr]; exact h.rsi
  · rw [f.gpr]; exact h.rcx
  · rw [f.gpr]; exact h.r11
  · rw [f.gpr]; exact h.r10
  · intro r h1 h2 h3 h4 h5 h6; rw [f.gpr]; exact h.other r h1 h2 h3 h4 h5 h6
  · rw [f.mem]; exact h.frame
  · intro k hk; rw [f.mem]; exact h.powers k hk
  · rw [f.mem]; exact h.mask
  · rw [f.mem]; exact h.poly
  · rw [f.mem]; exact h.rounds
  · rw [f.mem]; exact h.data
  · exact f.rd.trans h.rd
  · exact f.wr.trans h.wr

/-- A scratch write preserves reads outside the two changing buffers. -/
theorem work_read {s₀ : State} {m m' : Mem} (h : Frame [workR s₀] m m')
    (d n : Nat) (hd : d + n ≤ 512 ∨ 768 ≤ d) (hn : d + n ≤ 1024) :
    m'.readW (pp s₀ + BitVec.ofNat 64 d) (8 * n) =
      m.readW (pp s₀ + BitVec.ofNat 64 d) (8 * n) := by
  apply h.readW (r := ⟨pp s₀ + BitVec.ofNat 64 d, n⟩)
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact Offset.disjoint (pp s₀) hd (by omega) (by decide)
  · omega

theorem Env.buffer {s₀ s t : State} {P : Nat → Block}
    (h : Env s₀ P s) (f : BufferFrame s t) (hm : Frame [workR s₀] s.mem t.mem) :
    Env s₀ P t := by
  constructor
  · rw [f.gpr _ (by decide)]; exact h.rdi
  · rw [f.gpr _ (by decide)]; exact h.rsi
  · rw [f.gpr _ (by decide)]; exact h.rcx
  · rw [f.gpr _ (by decide)]; exact h.r11
  · rw [f.gpr _ (by decide)]; exact h.r10
  · intro r h1 h2 h3 h4 h5 h6; rw [f.gpr r h1]; exact h.other r h1 h2 h3 h4 h5 h6
  · refine h.frame.trans (hm.sub fun r hr => ?_)
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨pR s₀, by simp, Offset.sub_base _ (by decide)⟩
  · intro k hk
    rw [work_read hm (128 + 16 * k) 16 (by omega) (by omega)]
    exact h.powers k hk
  · exact (work_read hm 768 16 (by omega) (by omega)).trans h.mask
  · exact (work_read hm 784 16 (by omega) (by omega)).trans h.poly
  · exact (work_read hm 800 8 (by omega) (by omega)).trans h.rounds
  · exact (work_read hm 808 8 (by omega) (by omega)).trans h.data
  · exact f.rd.trans h.rd
  · exact f.wr.trans h.wr

end VG.Proof.Gcm.X86_64.StitchAvx8
