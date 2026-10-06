import VerifiedGarbage.Proof.Bignum.X86_64.AdxRect8Embed
import VerifiedGarbage.Proof.Bignum.Rectangular

/-! The invariant keeps the full product plus its pending row carry exact. -/
namespace VG.Proof.Bignum.X86_64.AdxRect8
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

def rawBase (w : Nat) := slot w aAcc+16

def rowRanges (w : Nat) : List (Nat × Nat) :=
  [(rawBase w,16*w),(carryOffset,8),(8*sFn 13,8)]

structure RowInv (s₀ : State) (B : Addr) (Z w a b i j₀ k : Nat) (mi : BitVec 64) (s : State) : Prop where
  scr : Scr s B Z
  hdr : Hdr s.mem B w mi
  rdi : s.gpr .rdi = B
  indexI : word s.mem B (8*sFn 12) = BitVec.ofNat 64 i
  indexJ : word s.mem B (8*sFn 13) = BitVec.ofNat 64 (j₀+8*k)
  carry : (word s.mem B carryOffset).toNat ≤ 1
  keep : Keep mmRegs s₀ s
  frame : Frm B (rowRanges w) s₀.mem s.mem
  endPtr : k=0 ∨ s.gpr .rsi = off B (rawBase w+8*(i+j₀+8*k))
  val : wv s.mem B (rawBase w) (2*w) +
      (2 : Nat)^(64*(i+j₀+8*(k+1))) * (word s.mem B carryOffset).toNat =
    wv s₀.mem B (rawBase w) (2*w) +
      (2 : Nat)^(64*(i+j₀)) * wv s₀.mem B (slot w a+8*i) 8 * wv s₀.mem B (slot w b+8*j₀) (8*k)

/-- Input arrays remain disjoint from the entire raw product and its counters. -/
theorem input_preserved {m m' : Mem} {B : Addr} {w a i n : Nat}
    (ha : a < 8) (h1 : a ≠ aAcc) (h2 : a ≠ aTmp) (hi : i+n ≤ w)
    (hZ : slot w 8 ≤ (2 : Nat)^64) (hf : Frm B (rowRanges w) m m') :
    wv m' B (slot w a+8*i) n = wv m B (slot w a+8*i) n := by
  have sa := slot_le (w := w) ha
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  apply hf.wv_eq
  · intro r hr
    simp only [rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [] <;>
      simp only [rawBase,carryOffset,sFn,slot,hdrBytes,aAcc,aTmp] at * <;> omega
  · omega

theorem rowStep_inv {s₀ s : State} {B : Addr} {Z w a b i j₀ k n : Nat} {mi : BitVec 64}
    (hZ : slot w 8 ≤ Z) (hw : w < (2 : Nat)^31) (hi : i+8 ≤ w)
    (ha : a < 8) (hb : b < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp) (hn : w = j₀+8*n) (hk : k < n)
    (h : RowInv s₀ B Z w a b i j₀ k mi s) :
    WP isa (AdxRect8.rowStep a b) s fun t =>
      t.zf = some (decide (k+1=n)) ∧ RowInv s₀ B Z w a b i j₀ (k+1) mi t := by
  have nowrap := h.scr.nowrap
  have Z64 : slot w 8 ≤ (2 : Nat)^64 := by omega
  have rt := slot_le (w := w) (show aTmp < 8 by decide)
  have rawZ : rawBase w+8*(2*w) ≤ Z := by unfold rawBase slot aAcc aTmp at *; omega
  refine WP.mono (rowStep_ok h.scr h.rdi h.hdr hZ hw hi (by omega)
    ha hb ha1 ha2 hb1 hb2 h.indexI h.indexJ)
    fun t ⟨zt,jt,eq,_,carry,ht,ft,ptr,kt⟩ => ?_
  have localFrame : Frm B ((rawBase w+8*(i+(j₀+8*k)),128)::[(carryOffset,8),(8*sFn 13,8)]) s.mem t.mem := ft
  have wider : Frm B (rowRanges w) s.mem t.mem := by
    intro x hx
    apply localFrame x
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    have a0 := hx (rawBase w,16*w) (by simp [rowRanges])
    have a1 := hx (carryOffset,8) (by simp [rowRanges])
    have a2 := hx (8*sFn 13,8) (by simp [rowRanges])
    rcases hr with rfl | rfl | rfl <;> simp only [] <;> omega
  have it : word t.mem B (8*sFn 12) = BitVec.ofNat 64 i := by
    rw [wider.word_eq (by
      intro r hr
      simp only [rowRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [] <;>
        simp only [rawBase,carryOffset,sFn,slot,hdrBytes,aAcc] at * <;> omega) (by decide)]
    exact h.indexI
  have va := input_preserved ha ha1 ha2 hi Z64 h.frame
  have vb := input_preserved hb hb1 hb2 (by omega : j₀+8*k+8 ≤ w) Z64 h.frame
  rw [← show rawBase w = slot w aAcc+16 from rfl] at eq
  generalize hp : (2 : Nat)^1024 = Q at eq
  generalize hq : (2 : Nat)^512 = R at eq
  have full := by
    exact (embed_value (e := rawBase w)
      (u := wv s.mem B (slot w a+8*i) 8) (v := wv s.mem B (slot w b+8*(j₀+8*k)) 8)
      (cin := (word s.mem B carryOffset).toNat) (cout := (word t.mem B carryOffset).toNat)
      (by omega : i+(j₀+8*k)+16 ≤ 2*w) (by omega : rawBase w+8*(2*w) ≤ (2 : Nat)^64)
      (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> simp only [] <;>
          simp only [rawBase,carryOffset,sFn,slot,hdrBytes,aAcc] <;> omega) localFrame eq)
  rw [← hp,← hq,va,vb] at full
  refine ⟨?_,⟨h.scr.congr kt.2.2,ht,(kt.gpr (by decide)).trans h.rdi,it,?_,carry h.carry,
    (h.keep.trans kt).mono (by decide),h.frame.trans wider,?_,?_⟩⟩
  · rw [zt]; exact congrArg some (decide_eq_decide.mpr (by omega))
  · simpa only [show j₀+8*(k+1)=(j₀+8*k)+8 by omega] using jt
  · apply Or.inr
    rw [ptr]
    apply congrArg (off B)
    unfold rawBase
    omega
  · have prev := h.val
    rw [show 8*(k+1)=8*k+8 by omega,wv_add]
    rw [show slot w b+8*j₀+8*(8*k)=slot w b+8*(j₀+8*k) by omega]
    rw [← Nat.pow_add 2 (64*(i+(j₀+8*k))) 1024,
      ← Nat.pow_add 2 (64*(i+(j₀+8*k))) 512] at full
    have p1 : 64*(i+(j₀+8*k))+1024 = 64*(i+j₀+8*((k+1)+1)) := by omega
    have p2 : 64*(i+(j₀+8*k))+512 = 64*(i+j₀+8*(k+1)) := by omega
    rw [p1,p2] at full
    rw [show 64*(i+(j₀+8*k))=64*(i+j₀)+64*(8*k) by omega,Nat.pow_add] at full
    exact VG.Proof.Bignum.Rectangular.extend_full prev full

end VG.Proof.Bignum.X86_64.AdxRect8
