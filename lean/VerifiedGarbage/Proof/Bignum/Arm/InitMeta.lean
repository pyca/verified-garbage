module

public import VerifiedGarbage.Impl.Bignum.Arm.MontInit
public import VerifiedGarbage.Proof.Bignum.Arm.Workspace

/-! # Eight bounded stores initialize the Montgomery metadata -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest wp_str)

def initMetaMem (s : State) (base : Addr) (tmp : Nat) : Mem :=
  ((((((((s.mem.writeW (off base (tmp + 0)) (s.gpr .r7)).writeW
     (off base (tmp + 4)) (s.gpr .r9)).writeW
     (off base (tmp + 8)) (s.gpr .r11)).writeW
     (off base (tmp + 12)) (s.gpr .r12)).writeW
     (off base (tmp + 16)) (s.gpr .r8)).writeW
     (off base (tmp + 20)) (s.gpr .r7)).writeW
     (off base (tmp + 24)) (s.gpr .r10)).writeW
     (off base (tmp + 28)) (s.gpr .r6))

theorem initMeta_ok (s : State) {base : BitVec 32} {size tmp : Nat}
    (ws : Workspace s base size) (fit : tmp + 32 ≤ size)
    (ptr : s.gpr .r5 = base + BitVec.ofNat 32 tmp) :
    WP isa (.block initMeta) s fun t =>
      t.mem = initMetaMem s (State.addr base) tmp ∧ Rest [] s t := by
  unfold initMeta
  refine wp_str (by decide) (ws.ea ptr (by omega)) (ws.write (by omega)) fun s1 u1 => ?_
  have w1 := ws.congr u1.wr
  have p1 := (congrFun u1.gpr .r5).trans ptr
  refine wp_str (by decide) (w1.ea p1 (by omega)) (w1.write (by omega)) fun s2 u2 => ?_
  have w2 := w1.congr u2.wr
  have p2 := (congrFun u2.gpr .r5).trans p1
  refine wp_str (by decide) (w2.ea p2 (by omega)) (w2.write (by omega)) fun s3 u3 => ?_
  have w3 := w2.congr u3.wr
  have p3 := (congrFun u3.gpr .r5).trans p2
  refine wp_str (by decide) (w3.ea p3 (by omega)) (w3.write (by omega)) fun s4 u4 => ?_
  have w4 := w3.congr u4.wr
  have p4 := (congrFun u4.gpr .r5).trans p3
  refine wp_str (by decide) (w4.ea p4 (by omega)) (w4.write (by omega)) fun s5 u5 => ?_
  have w5 := w4.congr u5.wr
  have p5 := (congrFun u5.gpr .r5).trans p4
  refine wp_str (by decide) (w5.ea p5 (by omega)) (w5.write (by omega)) fun s6 u6 => ?_
  have w6 := w5.congr u6.wr
  have p6 := (congrFun u6.gpr .r5).trans p5
  refine wp_str (by decide) (w6.ea p6 (by omega)) (w6.write (by omega)) fun s7 u7 => ?_
  have w7 := w6.congr u7.wr
  have p7 := (congrFun u7.gpr .r5).trans p6
  refine wp_str (by decide) (w7.ea p7 (by omega)) (w7.write (by omega)) fun s8 u8 => WP.block_nil ?_
  refine ⟨?_, ?_⟩
  · simp only [initMetaMem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, u7.gpr, u6.gpr, u5.gpr, u4.gpr, u3.gpr, u2.gpr, u1.gpr]
  · exact (u1.rest []).trans ((u2.rest []).trans ((u3.rest []).trans ((u4.rest []).trans ((u5.rest []).trans ((u6.rest []).trans ((u7.rest []).trans ((u8.rest []))))))))

end VG.Proof.Bignum.Arm
