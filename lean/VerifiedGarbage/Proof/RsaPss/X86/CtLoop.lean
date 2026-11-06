module

public import VerifiedGarbage.Proof.RsaPss.X86.CtComp
public import VerifiedGarbage.Proof.RsaPss.X86.CtSel
import VerifiedGarbage.Proof.RsaPss.X86.CtPad
import VerifiedGarbage.Proof.RsaPss.X86.Taint
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset

/-!
# RSASSA-PSS on x86: hashing, the compression loop

`CM`: the memory of the compression loop's state after `b` blocks, each
copied after the hash value at `oSt` and compressed into it, and the hash
value after block `lb` (the last of the padded message) selected into
`oSel`: that of `Y`'s first `lb + 1` blocks; and what the loop writes
(`loopW`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86.Wp VG.Impl.RsaPss.X86 VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.Proof.MdStream (Md)

/-- `Y`'s first `T` bytes, as a list. -/
def ylist (yv : Nat → Byte) (T : Nat) : List Byte := (List.range T).map yv

theorem ylist_getD {yv : Nat → Byte} {T j : Nat} (h : j < T) : (ylist yv T).getD j 0 = yv j := by
  simp [ylist, List.getD_eq_getElem?_getD, h]

/-- `cmp d, [b + o]`, and the carry and zero flags. -/
theorem wp_cmpm {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Fupd s s' → s'.cf = some (decide ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat)) →
      s'.zf = some (s.gpr d - s.mem.readW (addr B o) 32 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.mem ⟨b, o⟩) :: is)) s Q := by
  refine cons (s' := arithFlags s (s.gpr d - s.mem.readW (addr B o) 32)
    ((s.gpr d).toNat < (s.mem.readW (addr B o) 32).toNat)
    (subOverflow (s.gpr d) (s.mem.readW (addr B o) 32) (s.gpr d - s.mem.readW (addr B o) 32)))
    (by simp [exec, execAlu, readSrc_mem hb hin]) (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl rfl)

/-- `sub d, [b + o]`. -/
theorem wp_subm {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {B : BitVec 32} {o : Nat}
    (hb : s.gpr b = B) (hin : InRegions (s.rd ++ s.wr) (addr B o) 4)
    (k : ∀ s', Upd s s' d (s.gpr d - s.mem.readW (addr B o) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.mem ⟨b, o⟩) :: is)) s Q :=
  cons (by simp [exec, execAlu, readSrc_mem hb hin]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

variable {L : Lay} {scr : BitVec 32} (h : PssHash)

/-- A hash value kept by writes elsewhere. -/
theorem stateAt_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {o : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint (sR scr o h.N) r) : h.md.stateAt m' (sa scr o) = h.md.stateAt m (sa scr o) :=
  h.md.stateAt_congr fun _ hi => hf.bytes (R := sR scr o h.N) hd (by show h.N ≤ 2 ^ 64; have := h.N_le; omega_arith) hi

/-- What the compression loop writes. -/
abbrev loopW (L : Lay) (scr : BitVec 32) : List Region :=
  [sR scr oSt (h.N + h.B), sR scr oCW h.H.so, sR scr oSel h.N, slotR L sBi, L.LOW]

/-- The memory of the loop's state after `b` blocks, from `Y`'s bytes `yv`
(`T` of them), with `lb` the last block of the padded message. -/
structure CM (L : Lay) (scr : BitVec 32) (T : Nat) (yv : Nat → Byte) (lb b : Nat) (m : Mem) : Prop where
  y : ∀ i < T, m (sa scr (oY + i)) = yv i
  bi : m.readW (L.fr sBi) 32 = BitVec.ofNat 32 b
  st : h.md.stateAt m (sa scr oSt) = h.md.compressList h.ok.iv (ylist yv T) b
  sel : lb < b → h.md.stateAt m (sa scr oSel) = h.md.compressList h.ok.iv (ylist yv T) (lb + 1)

/-- `CM` kept by writes that miss `Y`, `sBi` and the hash values. -/
theorem CM.keep {T : Nat} {yv : Nat → Byte} {lb b : Nat} {m m' : Mem} (hm : CM h L scr T yv lb b m)
    {rs : List Region} (fr : Frame rs m m') (hT : oY + T < 2 ^ 64)
    (dY : ∀ r ∈ rs, Region.Disjoint (sR scr oY T) r) (dB : ∀ r ∈ rs, (slotR L sBi).Disjoint r)
    (dS : ∀ r ∈ rs, Region.Disjoint (sR scr oSt h.N) r) (dE : ∀ r ∈ rs, Region.Disjoint (sR scr oSel h.N) r) :
    CM h L scr T yv lb b m' :=
  ⟨sbytes_keep fr dY hT hm.y, slot_keep fr dB hm.bi, by rw [stateAt_keep h fr dS, hm.st],
    fun hl => by rw [stateAt_keep h fr dE, hm.sel hl]⟩

end VG.Proof.RsaPss.X86
