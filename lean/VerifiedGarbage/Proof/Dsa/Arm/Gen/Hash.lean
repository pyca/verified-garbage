module

public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Bytes
public import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # DSA parameter generation on ARMv7: a hash of one block

`hash L Gh dst` (`Impl/Dsa/Arm/Generation.lean`) hashes the block at
`sMsg`: the initial hash value into `sState` (`ivStore_ok`), the
compression function on it (`MdStream.Arm.compressAt_ok`), and the hash
value's words big-endian at `dst` (`MdStream.Arm.out32_ok`). `HashOk Gh`
is what the proof needs of the hash function: its compression function
verified, as the streaming proofs see it, and its digest of a message of
fewer than 56 bytes as that compression of its one padded block.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_movw wp_mov wp_dp wp_str op2_reg op2_imm dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

/-! ## The initial hash value -/

/-- `ivStore` from word `n` on. -/
def ivAt (iv : List (BitVec 32)) (n : Nat) : List Instr :=
  (iv.zipIdx n).flatMap fun (v, i) => const v ++ [.str .r1 .r0 (4 * i)]

theorem ivStore_eq (iv : List (BitVec 32)) : ivStore iv = ivAt iv 0 := rfl

theorem wp_movt {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {imm : BitVec 16}
    (k : ∀ s', Upd s s' d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movt d imm :: is)) s Q :=
  VG.Proof.X25519.Arm.WP.cons rfl (k _ (VG.Proof.X25519.Arm.Upd.setReg _ _ _))

theorem ivAt_ok {p : BitVec 32} {R : Region} : ∀ (iv : List (BitVec 32)) (n : Nat) (s : State) (rest : List Instr)
    (Q : State → Prop), s.gpr .r0 = p → 4 * (n + iv.length) ≤ 4096 → p.toNat + 4 * (n + iv.length) ≤ 2 ^ 32 →
    R ∈ s.wr → (∀ j < iv.length, R.Contains (State.addr p + BitVec.ofNat 64 (4 * (n + j))) 4) →
    (∀ t, Rest [.r1] s t → Frame [⟨State.addr p + BitVec.ofNat 64 (4 * n), 4 * iv.length⟩] s.mem t.mem →
      (∀ j (hj : j < iv.length), t.mem.readW (State.addr p + BitVec.ofNat 64 (4 * (n + j))) 32 = iv[j]) →
      WP isa (.block rest) t Q) →
    WP isa (.block (ivAt iv n ++ rest)) s Q
  | [], _, s, _, _, _, _, _, _, _, k => k s (Rest.refl _ _) (Frame.refl _ _) fun _ hj => absurd hj (by simp)
  | v :: vs, n, s, rest, Q, h0, hn, hf, hR, hc, k => by
    simp only [List.length_cons] at hn hf hc
    simp only [ivAt, List.zipIdx_cons, List.flatMap_cons, const, List.cons_append, List.nil_append]
    refine wp_movw fun s₁ u₁ => wp_movt fun s₂ u₂ => ?_
    have e0 : s₂.gpr .r0 = p := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h0]
    have ea : State.addr (s₂.gpr .r0 + BitVec.ofNat 32 (4 * n)) = State.addr p + BitVec.ofNat 64 (4 * n) := by
      rw [e0]; exact addr_add (by omega)
    have hc0 := hc 0 (by omega)
    rw [Nat.add_zero] at hc0
    refine wp_str (by omega) ea ⟨R, by rw [u₂.wr, u₁.wr]; exact hR, hc0⟩ fun s₃ m₃ => ?_
    have v₂ : s₂.gpr .r1 = v := by rw [u₂.gpr, u₁.gpr]; exact VG.Arm.movw_movt v
    refine ivAt_ok vs (n + 1) s₃ rest Q (by rw [m₃.gpr, e0]) (by omega) (by omega)
      (by rw [m₃.wr, u₂.wr, u₁.wr]; exact hR)
      (fun j hj => by rw [show n + 1 + j = n + (j + 1) by omega]; exact hc (j + 1) (by omega))
      fun t R' F' W' => ?_
    have base : Region.Sub ⟨State.addr p + BitVec.ofNat 64 (4 * (n + 1)), 4 * vs.length⟩
        ⟨State.addr p + BitVec.ofNat 64 (4 * n), 4 * (vs.length + 1)⟩ := by
      rw [show 4 * (n + 1) = 4 * n + 4 by omega, ← Offset.add_add]
      exact Offset.sub_base _ (by omega)
    refine k t (((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans ((m₃.rest _).trans R')) ?_ fun j hj => ?_
    · have f₃ : Frame [⟨State.addr p + BitVec.ofNat 64 (4 * n), 4 * (vs.length + 1)⟩] s.mem s₃.mem := by
        rw [m₃.mem, u₂.mem, u₁.mem]
        refine Frame.writeW (Frame.refl _ s.mem) List.mem_cons_self (w := 32) (s₂.gpr .r1) ?_
        show (_ - _ : Addr).toNat + 4 ≤ _
        rw [BitVec.sub_self, BitVec.toNat_zero]; show 0 + 4 ≤ 4 * (vs.length + 1); omega
      exact f₃.trans (F'.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_cons_self, base⟩)
    · cases j with
      | zero =>
        rw [Nat.add_zero]
        have d : Region.Disjoint ⟨State.addr p + BitVec.ofNat 64 (4 * n), 4⟩
            ⟨State.addr p + BitVec.ofNat 64 (4 * (n + 1)), 4 * vs.length⟩ := by
          rw [show 4 * (n + 1) = 4 * n + 4 by omega, ← Offset.add_add]
          exact (Offset.disjoint_base _ (Nat.le_refl 4) (by omega)).symm
        rw [F'.readW (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact d) (by decide), m₃.mem, Mem.readW_writeW_self32, v₂]
        rfl
      | succ j =>
        have := W' j (by simp at hj; omega)
        rw [show n + (j + 1) = n + 1 + j by omega]
        exact this

/-! ## What the proof needs of the hash function -/

/-- The block of a message of fewer than 56 bytes. -/
def blk {B N L : Nat} (md : MdStream.Md B N L) (msg : List Byte) : List Byte :=
  msg ++ [0x80] ++ List.replicate (55 - msg.length) 0 ++ md.lenBytes msg.length

structure HashOk (Gh : Hash) where
  P : VG.Impl.MdStream.Arm.Params
  md : MdStream.Md P.B P.N P.L
  hB : P.B = 64
  hL : P.L = 8
  hN : P.N = 4 * Gh.k
  hso : P.so = 112
  hk : Gh.k ≤ 8
  hk0 : 0 < Gh.k
  ivLen : Gh.iv.length = Gh.k
  callee : MdStream.Arm.CalleeOk md Gh.code
  ct : ConstantTime isa (MdStream.Arm.compressK md).pre (MdStream.Arm.compressK md).pub Gh.code
  /-- The initial hash value. -/
  H0 : md.HV
  iv : ∀ (m : Mem) (p : Addr), (∀ j (hj : j < Gh.iv.length), m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = Gh.iv[j]) →
    md.stateAt m p = H0
  digest : ∀ (m : Mem) (p : Addr), md.digest (md.stateAt m p) =
    (List.range Gh.k).flatMap fun j => MdStream.bytes32 true (m.readW (p + BitVec.ofNat 64 (4 * j)) 32)
  /-- The hash function. -/
  H : List Byte → List Byte
  hash : ∀ msg, msg.length < 56 → H msg = md.digest (md.compress H0 (md.parse fun t => (blk md msg).getD t 0))
  /-- The taint analysis of the code before and after the call, which
  depends on the hash function only through its initial hash value and its
  words: checked on each instance. -/
  cert1 : ∀ L, Cert8 (.block (scr L .r0 sState ++ ivStore Gh.iv ++ scr L .r1 sMsg ++ scr L .r3 sA))
  cert3 : ∀ L dst, ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r8]) (.block (scr L .r6 dst ++
      VG.Impl.MdStream.Arm.out32 Gh.k true ++ [.mov .r9 (.imm (BitVec.ofNat 32 (L / 4)))])) hc).isSome = true

end VG.Proof.Dsa.Arm.Gen
