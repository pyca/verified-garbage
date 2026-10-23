module

public import VerifiedGarbage.Proof.Mont.PPC64LE.Words
import VerifiedGarbage.Proof.Mont.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# Deterministic ECDSA on PPC64LE: steps

One instruction at a time, with the state after it abstract: what it keeps
(`Kp`, the registers it does not write and the permissions, `sp` and `lr`),
its memory and the value it writes, so that a block's symbolic execution
never builds a nest of writes.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.PPC64LE

open VG VG.PPC64LE
open VG.Proof.Mont.PPC64LE (Kp wp_step write_gpr)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem kp_write (s : State) (d : Reg) (v : BitVec 64) : Kp [d] s (s.write d v) :=
  Kp.write s v (List.mem_singleton_self _)

theorem write_self (s : State) (d : Reg) (v : BitVec 64) : (s.write d v).gpr d = v := by
  simp only [write_gpr, ite_true]

/-- A register write, from what the instruction does. -/
theorem stepW {i : Instr} {d : Reg} {v : BitVec 64} (h : exec i s = some (s.write d v))
    (k : ∀ s', Kp [d] s s' → s'.mem = s.mem → s'.gpr d = v → WP isa (.block is) s' Q) :
    WP isa (.block (i :: is)) s Q :=
  wp_step h (k _ (kp_write s d v) rfl (write_self s d v))

/-- A store, from what the instruction does. -/
theorem stepM {i : Instr} {m : Mem} (h : exec i s = some { s with mem := m })
    (k : ∀ s', Kp [] s s' → s'.gpr = s.gpr → s'.mem = m → WP isa (.block is) s' Q) :
    WP isa (.block (i :: is)) s Q :=
  wp_step h (k _ (Kp.store s m []) rfl rfl)

theorem stepAddSp {d : Reg} {imm : Nat} (h : imm < 2 ^ 15)
    (k : ∀ s', Kp [d] s s' → s'.mem = s.mem → s'.gpr d = s.sp + BitVec.ofNat 64 imm → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  stepW (by simp only [exec, h, ite_true]) k

theorem stepLi {d : Reg} {imm : Nat} (h : imm < 2 ^ 15)
    (k : ∀ s', Kp [d] s s' → s'.mem = s.mem → s'.gpr d = BitVec.ofNat 64 imm → WP isa (.block is) s' Q) :
    WP isa (.block (.li d imm :: is)) s Q :=
  stepW (exec_li h) k

theorem stepAddi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm < 2 ^ 15)
    (k : ∀ s', Kp [d] s s' → s'.mem = s.mem → s'.gpr d = s.gpr n + BitVec.ofNat 64 imm →
      WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  stepW (exec_addi hn h) k

theorem stepSubi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm ≤ 2 ^ 15)
    (k : ∀ s', Kp [d] s s' → s'.mem = s.mem → s'.gpr d = s.gpr n - BitVec.ofNat 64 imm →
      WP isa (.block is) s' Q) :
    WP isa (.block (.subi d n imm :: is)) s Q :=
  stepW (exec_subi hn h) k

theorem stepAdd {d n m : Reg}
    (k : ∀ s', Kp [d] s s' → s'.mem = s.mem → s'.gpr d = s.gpr n + s.gpr m → WP isa (.block is) s' Q) :
    WP isa (.block (.add d n m :: is)) s Q :=
  stepW exec_add k

theorem stepSub {d n m : Reg}
    (k : ∀ s', Kp [d] s s' → s'.mem = s.mem → s'.gpr d = s.gpr n - s.gpr m → WP isa (.block is) s' Q) :
    WP isa (.block (.sub d n m :: is)) s Q :=
  stepW exec_sub k

theorem stepAnd {d n m : Reg}
    (k : ∀ s', Kp [d] s s' → s'.mem = s.mem → s'.gpr d = (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  stepW exec_logic k

theorem stepXor {d n m : Reg}
    (k : ∀ s', Kp [d] s s' → s'.mem = s.mem → s'.gpr d = (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  stepW exec_logic k

theorem stepLsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Kp [d] s s' → s'.mem = s.mem → s'.gpr d = s.gpr n >>> sh → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .d d n sh :: is)) s Q :=
  stepW (exec_lsr_d h) k

theorem stepLis {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Kp [d] s s' → s'.mem = s.mem → s'.gpr d = (imm ++ (0 : BitVec 16)).signExtend 64 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.lis d imm :: is)) s Q :=
  stepW exec_lis k

theorem stepOri {d n : Reg} {imm : BitVec 16}
    (k : ∀ s', Kp [d] s s' → s'.mem = s.mem → s'.gpr d = (s.gpr n ||| imm.setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.ori d n imm :: is)) s Q :=
  stepW exec_ori k

theorem stepOris {d n : Reg} {imm : BitVec 16}
    (k : ∀ s', Kp [d] s s' → s'.mem = s.mem → s'.gpr d = (s.gpr n ||| imm.setWidth 64 <<< 16) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.oris d n imm :: is)) s Q :=
  stepW exec_oris k

theorem stepLd {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Kp [t] s s' → s'.mem = s.mem → s'.gpr t = s.mem.readW a 64 → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t n off :: is)) s Q :=
  stepW (by rw [exec_load_d hn ho (by rw [ha]; exact hin), ha]) k

theorem stepLwz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Kp [t] s s' → s'.mem = s.mem → s'.gpr t = (s.mem.readW a 32).setWidth 64 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.load .w t n off :: is)) s Q :=
  stepW (by rw [exec_load_w hn ho (by rw [ha]; exact hin), ha]) k

theorem stepLwbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hin : InRegions (s.rd ++ s.wr) ea 4)
    (k : ∀ s', Kp [t] s s' → s'.mem = s.mem → s'.gpr t = (rev32 (s.mem.readW ea 32)).setWidth 64 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.loadRev .w t a b :: is)) s Q :=
  stepW (by rw [exec_loadRev_w hn (by rw [hea]; exact hin), hea]) k

theorem stepStd {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Kp [] s s' → s'.gpr = s.gpr → s'.mem = s.mem.writeW a (s.gpr t) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q :=
  stepM (by rw [exec_store_d hn ho (by rw [ha]; exact hout), ha]) k

theorem stepStw {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Kp [] s s' → s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr t).setWidth 32) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.store .w t n off :: is)) s Q :=
  stepM (by rw [exec_store_w hn ho (by rw [ha]; exact hout), ha]) k

theorem stepStwbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hout : InRegions s.wr ea 4)
    (k : ∀ s', Kp [] s s' → s'.gpr = s.gpr → s'.mem = s.mem.writeW ea (rev32 ((s.gpr t).setWidth 32)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.storeRev .w t a b :: is)) s Q :=
  stepM (by rw [exec_storeRev_w hn (by rw [hea]; exact hout), hea]) k

theorem stepStb {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Kp [] s s' → s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr t).setWidth 8) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.stb t n off :: is)) s Q :=
  stepM (by rw [exec_stb hn ho (by rw [ha]; exact hout), ha]; rfl) k

end

end VG.Proof.Ecdsa.Rfc6979.PPC64LE
