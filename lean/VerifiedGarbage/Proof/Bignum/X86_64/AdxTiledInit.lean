import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledCounter
import VerifiedGarbage.Proof.Bignum.X86_64.OpAt

namespace VG.Proof.Bignum.X86_64.AdxTiledProduct
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Proof.Bignum.X86_64.AdxRect8 (rawBase)
open VG.Impl.Bignum.X86_64.AdxRect8 (carryOffset)

def ranges (w : Nat) : List (Nat × Nat) := [(rawBase w,16*w),(8*sFn 12,32)]

theorem frame_hdr {m m' : Mem} {B : Addr} {w : Nat} {mi : BitVec 64}
    (hh : Hdr m B w mi) (hf : Frm B (ranges w) m m') : Hdr m' B w mi := by
  have low (k : Nat) (hk : k < 16) : word m' B (8*k) = word m B (8*k) := by
    apply hf.word_eq
    · intro r hr
      simp only [ranges,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> simp only [] <;> simp only [rawBase,slot,hdrBytes,sFn] <;> omega
    · omega
  exact ⟨(low sW (by decide)).trans hh.hw,(low sMinv (by decide)).trans hh.hminv,
    fun k hk => (low (sArr k) (by unfold sArr; omega)).trans (hh.harr k hk)⟩

theorem frame_ops {m m' : Mem} {B : Addr} {w : Nat} {ps : List (Nat × Nat)}
    (hv : Ops m B w ps) (hf : Frm B (ranges w) m m') : Ops m' B w ps :=
  hv.of_frm hf fun r hr => by
    simp only [ranges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [] <;> simp only [rawBase,slot,hdrBytes,sFn] <;> omega

theorem input_preserved {m m' : Mem} {B : Addr} {w a i n : Nat}
    (ha : a < 8) (h1 : a ≠ aAcc) (h2 : a ≠ aTmp) (hi : i+n ≤ w)
    (hZ : slot w 8 ≤ (2 : Nat)^64) (hf : Frm B (ranges w) m m') :
    wv m' B (slot w a+8*i) n = wv m B (slot w a+8*i) n := by
  have sa := slot_le (w := w) ha
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  apply hf.wv_eq
  · intro r hr
    simp only [ranges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> simp only [] <;>
      simp only [rawBase,sFn,slot,hdrBytes,aAcc,aTmp] at * <;> omega
  · omega

theorem rowInit_ok {s : State} {B : Addr} {Z w : Nat}
    (hs : Scr s B Z) (hd : s.gpr .rdi = B) (hZ : slot w 8 ≤ Z) :
    WP isa (.block AdxTiledProduct.rowInit) s fun t =>
      word t.mem B carryOffset = 0 ∧ word t.mem B (8*sFn 13) = 0 ∧
      Outside B (8*sFn 13) 16 s.mem t.mem ∧ Keep [.rax] s t := by
  have hn := hs.nowrap
  have cZ : carryOffset+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 14 < 32 by decide); unfold carryOffset; omega
  have jZ : 8*sFn 13+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sFn 13 < 32 by decide); omega
  have body : WP isa (.block AdxTiledProduct.rowInit) s fun t =>
      t.mem = (s.mem.writeW (off B carryOffset) (0 : BitVec 64)).writeW (off B (8*sFn 13)) (0 : BitVec 64) ∧ Keep [.rax] s t := by
    apply WP.keep [.rax] (Q := fun t => t.mem = (s.mem.writeW (off B carryOffset) (0 : BitVec 64)).writeW (off B (8*sFn 13)) (0 : BitVec 64)) _ rfl
    unfold AdxTiledProduct.rowInit
    xrun [State.ea,hdr,hd,hdrOff,carryOffset,hs.st (show 8*sFn 14+8 ≤ Z from cZ),hs.st jZ]
    rfl
  refine WP.mono body fun t ⟨mt,kt⟩ => ?_
  have c := writeW_outside s.mem B (0 : BitVec 64) (by omega : carryOffset+8 ≤ 2^64)
  have j := writeW_outside (s.mem.writeW (off B carryOffset) (0 : BitVec 64)) B (0 : BitVec 64) (by omega : 8*sFn 13+8 ≤ 2^64)
  refine ⟨?_,?_,?_,kt⟩
  · rw [mt,j.word (by unfold carryOffset sFn; omega) (by omega),word_writeW_self]
  · rw [mt,word_writeW_self]
  · rw [mt]
    exact (c.mono (o' := 8*sFn 13) (n' := 16) (by unfold carryOffset sFn; omega) (by unfold carryOffset sFn; omega)).trans
      (j.mono (o' := 8*sFn 13) (n' := 16) (by omega) (by omega))

end VG.Proof.Bignum.X86_64.AdxTiledProduct
