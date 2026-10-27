module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Impl.Scrypt.AArch64.Transfer
import VerifiedGarbage.Proof.Scrypt.AArch64.Transfer.Memory
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Scrypt.Memory
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Spec.Scrypt.Contract

@[expose] public section
namespace VG.Proof.Scrypt.AArch64.Transfer
open VG VG.AArch64 VG.Spec.Scrypt
open VG.Impl.Scrypt.AArch64.Transfer (vr)
open VG.Proof.Scrypt.Memory (add_ofNat sub_off)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)

theorem vr_ne {i j : Nat} (hi : i < 8) (hj : j < 8) (h : i ≠ j) : vr i ≠ vr j := by
  have key : ∀ i, i < 8 → ∀ j, j < 8 → i ≠ j → vr i ≠ vr j := by decide
  exact key i hi j hj h

theorem exec_loadQ {s : State} {t : VReg} {b : Reg} {off : Nat}
    (ho : off % 16 = 0 ∧ off < 65536)
    (hi : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t b off) s = some (s.setV t (s.mem.readW (s.gpr b + BitVec.ofNat 64 off) 128)) := by
  simp only [exec,VG.AArch64.addr,show off < 4096*16 by omega,ho,and_self,ite_true,
    Option.bind_some,State.load,hi,Option.map_some,Mem.readW,BitVec.setWidth_eq]

theorem exec_storeQ {s : State} {t : VReg} {b : Reg} {off : Nat}
    (ho : off % 16 = 0 ∧ off < 65536)
    (hi : InRegions s.wr (s.gpr b + BitVec.ofNat 64 off) 16) :
    exec (.strq t b off) s = some {s with mem := s.mem.writeW (s.gpr b + BitVec.ofNat 64 off) (s.v t)} := by
  simp only [exec,VG.AArch64.addr,show off < 4096*16 by omega,ho,and_self,ite_true,
    Option.bind_some,State.store,hi,Mem.writeW,BitVec.setWidth_eq]

theorem exec_xorQ {s : State} {d n m : VReg} :
    exec (.vop (.logic .eor d n m)) s = some (s.setV d (s.v n ^^^ s.v m)) := rfl

structure LI (s₀ : State) (b : Reg) (v i : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  loaded : ∀ j < 4, j < i → s.v (vr (v+j)) = s₀.mem.readW (s₀.gpr b + BitVec.ofNat 64 (16*j)) 128
  keep : ∀ r, (∀ j < i, r ≠ vr (v+j)) → s.v r = s₀.v r

theorem load_step {s₀ s : State} {b : Reg} {v i : Nat} (hv : v = 0 ∨ v = 4) (hi : i < 4)
    (hin : ∀ j < 4, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr b + BitVec.ofNat 64 (16*j)) 16)
    (h : LI s₀ b v i s) :
    WP isa (.block [.ldrq (vr (v+i)) b (16*i)]) s (LI s₀ b v (i+1)) := by
  have ir : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 (16*i)) 16 := by
    rw [h.rd,h.wr,h.gpr]; exact hin i hi
  apply WP.of_runBlock
  simp only [runBlock_cons,runStep_some,runBlock_nil,
    exec_loadQ (show 16*i % 16 = 0 ∧ 16*i < 65536 by omega) ir,
    isa,Option.some.injEq,exists_eq_left']
  refine ⟨h.gpr,h.mem,h.rd,h.wr,h.sp,?_,?_⟩
  · intro j hj hji
    rcases Nat.lt_succ_iff_lt_or_eq.mp hji with lt | rfl
    · have ne : vr (v+j) ≠ vr (v+i) := vr_ne (by rcases hv with rfl | rfl <;> omega)
        (by rcases hv with rfl | rfl <;> omega) (by omega)
      simp only [State.setV,ne,ite_false]
      exact h.loaded j hj lt
    · simp only [State.setV,ite_true,h.mem,h.gpr]
  · intro r hr
    simp only [State.setV,hr i (by omega),ite_false]
    exact h.keep r fun j hj => hr j (by omega)

theorem loads_ok {s₀ : State} {b : Reg} {v : Nat} (hv : v = 0 ∨ v = 4)
    (hin : ∀ j < 4, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr b + BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block (VG.Impl.Scrypt.AArch64.Transfer.loads b v)) s₀ (LI s₀ b v 4) := by
  have eq : VG.Impl.Scrypt.AArch64.Transfer.loads b v =
      (List.range 4).flatMap (fun j => [.ldrq (vr (v+j)) b (16*j)]) := by
    rfl
  rw [eq]
  exact wp_range_flatMap (M := isa) (LI s₀ b v) (fun i s hi h => load_step hv hi hin h)
    4 (by omega) s₀ ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ h => by omega,fun _ _ => rfl⟩
def writeQ4 (m : Mem) (d : Addr) (f : Nat → BitVec 128) : Mem :=
  (((m.writeW (d + BitVec.ofNat 64 (16*0)) (f 0)).writeW (d + BitVec.ofNat 64 (16*1)) (f 1)).writeW
    (d + BitVec.ofNat 64 (16*2)) (f 2)).writeW (d + BitVec.ofNat 64 (16*3)) (f 3)

structure Stored (s₀ : State) (b : Reg) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = writeQ4 s₀.mem (s₀.gpr b) (fun j => s₀.v (vr j))

theorem stores_ok (s₀ : State) (b : Reg)
    (hout : ∀ j < 4, InRegions s₀.wr (s₀.gpr b + BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block (VG.Impl.Scrypt.AArch64.Transfer.stores b)) s₀ (Stored s₀ b) := by
  change WP isa (.block [.strq (vr 0) b 0,.strq (vr 1) b 16,.strq (vr 2) b 32,.strq (vr 3) b 48]) s₀ _
  let s₁ : State := {s₀ with mem := s₀.mem.writeW (s₀.gpr b + BitVec.ofNat 64 0) (s₀.v (vr 0))}
  let s₂ : State := {s₁ with mem := s₁.mem.writeW (s₀.gpr b + BitVec.ofNat 64 16) (s₀.v (vr 1))}
  let s₃ : State := {s₂ with mem := s₂.mem.writeW (s₀.gpr b + BitVec.ofNat 64 32) (s₀.v (vr 2))}
  let s₄ : State := {s₃ with mem := s₃.mem.writeW (s₀.gpr b + BitVec.ofNat 64 48) (s₀.v (vr 3))}
  refine WP.block_cons_iff.mpr ⟨s₁,exec_storeQ (s := s₀) (by decide) (hout 0 (by omega)),?_⟩
  refine WP.block_cons_iff.mpr ⟨s₂,exec_storeQ (s := s₁) (by decide) (hout 1 (by omega)),?_⟩
  refine WP.block_cons_iff.mpr ⟨s₃,exec_storeQ (s := s₂) (by decide) (hout 2 (by omega)),?_⟩
  refine WP.block_cons_iff.mpr ⟨s₄,exec_storeQ (s := s₃) (by decide) (hout 3 (by omega)),?_⟩
  exact WP.block_nil ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem writeQ4_copy (m m' : Mem) (d a : Addr) :
    writeQ4 m d (fun j => m'.readW (a + BitVec.ofNat 64 (16*j)) 128) =
      writeBytes m d (bytesAt m' a 64) := by
  simp only [writeQ4,Nat.reduceMul,BitVec.add_zero]
  rw [VG.Proof.Scrypt.Memory.writeW_readW m m' d a 16,
    VG.Proof.Scrypt.Memory.writeW_readW _ m' (d + BitVec.ofNat 64 16) (a + BitVec.ofNat 64 16) 16,
    VG.Proof.Scrypt.Memory.writeW_readW _ m' (d + BitVec.ofNat 64 32) (a + BitVec.ofNat 64 32) 16,
    VG.Proof.Scrypt.Memory.writeW_readW _ m' (d + BitVec.ofNat 64 48) (a + BitVec.ofNat 64 48) 16]
  have join (n : Nat) (hn : n ≤ 48) :
      writeBytes (writeBytes m d (bytesAt m' a n)) (d + BitVec.ofNat 64 n)
        (bytesAt m' (a + BitVec.ofNat 64 n) 16) = writeBytes m d (bytesAt m' a (n+16)) := by
    rw [VG.Proof.Scrypt.Memory.bytesAt_add]
    simpa only [VG.Proof.Scrypt.Memory.bytesAt_length] using
      VG.Proof.Sha256.Stream.writeBytes_append m d (bytesAt m' a n)
        (bytesAt m' (a + BitVec.ofNat 64 n) 16) (by simp [bytesAt]; omega)
  rw [join 16 (by omega),join 32 (by omega),join 48 (by omega)]

theorem copyPacket_ok (s₀ : State)
    (hin : ∀ j < 4, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x9 + BitVec.ofNat 64 (16*j)) 16)
    (hout : ∀ j < 4, InRegions s₀.wr (s₀.gpr .x10 + BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block VG.Impl.Scrypt.AArch64.Transfer.copyPacket) s₀ fun s =>
      s.gpr = s₀.gpr ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      s.mem = writeBytes s₀.mem (s₀.gpr .x10) (bytesAt s₀.mem (s₀.gpr .x9) 64) := by
  apply WP.block_append
  refine WP.mono (loads_ok (Or.inl rfl) hin) fun a ha => ?_
  refine WP.mono (stores_ok a .x10 (by intro j hj; rw [ha.wr,ha.gpr]; exact hout j hj)) fun s hs => ?_
  refine ⟨hs.gpr.trans ha.gpr,hs.rd.trans ha.rd,hs.wr.trans ha.wr,hs.sp.trans ha.sp,?_⟩
  rw [hs.mem,ha.mem,ha.gpr]
  have eq (j : Nat) (hj : j < 4) : a.v (vr j) = s₀.mem.readW (s₀.gpr .x9 + BitVec.ofNat 64 (16*j)) 128 := by
    simpa only [Nat.zero_add] using ha.loaded j hj hj
  simp only [writeQ4]
  rw [eq 0 (by omega),eq 1 (by omega),eq 2 (by omega),eq 3 (by omega)]
  exact writeQ4_copy _ _ _ _

structure Xored (s₀ s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  words : ∀ j < 4, s.v (vr j) = s₀.v (vr j) ^^^ s₀.v (vr (4+j))

theorem xors_ok (s₀ : State) :
    WP isa (.block VG.Impl.Scrypt.AArch64.Transfer.xors) s₀ (Xored s₀) := by
  change WP isa (.block [.vop (.logic .eor (vr 0) (vr 0) (vr 4)),
    .vop (.logic .eor (vr 1) (vr 1) (vr 5)),.vop (.logic .eor (vr 2) (vr 2) (vr 6)),
    .vop (.logic .eor (vr 3) (vr 3) (vr 7))]) s₀ _
  refine WP.block_cons_iff.mpr ⟨_,exec_xorQ,?_⟩
  refine WP.block_cons_iff.mpr ⟨_,exec_xorQ,?_⟩
  refine WP.block_cons_iff.mpr ⟨_,exec_xorQ,?_⟩
  refine WP.block_cons_iff.mpr ⟨_,exec_xorQ,?_⟩
  refine WP.block_nil ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro j hj
  obtain rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  all_goals rfl

theorem writeQ4_xor (m m' : Mem) (d a b : Addr) :
    writeQ4 m d (fun j => m'.readW (a + BitVec.ofNat 64 (16*j)) 128 ^^^
      m'.readW (b + BitVec.ofNat 64 (16*j)) 128) =
      writeBytes m d (VG.Spec.Pbkdf2.xorBytes (bytesAt m' a 64) (bytesAt m' b 64)) := by
  simp only [writeQ4,Nat.reduceMul,BitVec.add_zero]
  rw [writeW_xor 16 m m' d a b,
    writeW_xor 16 _ m' (d + BitVec.ofNat 64 16) (a + BitVec.ofNat 64 16) (b + BitVec.ofNat 64 16),
    writeW_xor 16 _ m' (d + BitVec.ofNat 64 32) (a + BitVec.ofNat 64 32) (b + BitVec.ofNat 64 32),
    writeW_xor 16 _ m' (d + BitVec.ofNat 64 48) (a + BitVec.ofNat 64 48) (b + BitVec.ofNat 64 48)]
  have join (n : Nat) (hn : n ≤ 48) :
      writeBytes (writeBytes m d (VG.Spec.Pbkdf2.xorBytes (bytesAt m' a n) (bytesAt m' b n)))
        (d + BitVec.ofNat 64 n)
        (VG.Spec.Pbkdf2.xorBytes (bytesAt m' (a + BitVec.ofNat 64 n) 16)
          (bytesAt m' (b + BitVec.ofNat 64 n) 16)) =
      writeBytes m d (VG.Spec.Pbkdf2.xorBytes (bytesAt m' a (n+16)) (bytesAt m' b (n+16))) := by
    rw [VG.Proof.Scrypt.Memory.bytesAt_add,VG.Proof.Scrypt.Memory.bytesAt_add,
      VG.Spec.Pbkdf2.xorBytes,VG.Spec.Pbkdf2.xorBytes,VG.Spec.Pbkdf2.xorBytes,
      List.zipWith_append (by simp [bytesAt])]
    simpa only [VG.Spec.Pbkdf2.xorBytes,List.length_zipWith,VG.Proof.Scrypt.Memory.bytesAt_length,Nat.min_self] using
      VG.Proof.Sha256.Stream.writeBytes_append m d
        (VG.Spec.Pbkdf2.xorBytes (bytesAt m' a n) (bytesAt m' b n))
        (VG.Spec.Pbkdf2.xorBytes (bytesAt m' (a + BitVec.ofNat 64 n) 16)
          (bytesAt m' (b + BitVec.ofNat 64 n) 16)) (by simp [VG.Spec.Pbkdf2.xorBytes,bytesAt]; omega)
  rw [join 16 (by omega),join 32 (by omega),join 48 (by omega)]

theorem xorPacket_ok (s₀ : State)
    (hinx : ∀ j < 4, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x9 + BitVec.ofNat 64 (16*j)) 16)
    (hiny : ∀ j < 4, InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x10 + BitVec.ofNat 64 (16*j)) 16)
    (hout : ∀ j < 4, InRegions s₀.wr (s₀.gpr .x11 + BitVec.ofNat 64 (16*j)) 16) :
    WP isa (.block VG.Impl.Scrypt.AArch64.Transfer.xorPacket) s₀ fun s =>
      s.gpr = s₀.gpr ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp ∧
      s.mem = writeBytes s₀.mem (s₀.gpr .x11)
        (VG.Spec.Pbkdf2.xorBytes (bytesAt s₀.mem (s₀.gpr .x9) 64) (bytesAt s₀.mem (s₀.gpr .x10) 64)) := by
  apply WP.block_append
  apply WP.block_append
  apply WP.block_append
  refine WP.mono (loads_ok (Or.inl rfl) hinx) fun a ha => ?_
  refine WP.mono (loads_ok (b := .x10) (Or.inr rfl)
    (by intro j hj; rw [ha.rd,ha.wr,ha.gpr]; exact hiny j hj)) fun b hb => ?_
  refine WP.mono (xors_ok b) fun c hc => ?_
  refine WP.mono (stores_ok c .x11
    (by intro j hj; rw [hc.wr,hb.wr,ha.wr,hc.gpr,hb.gpr,ha.gpr]; exact hout j hj)) fun s hs => ?_
  refine ⟨hs.gpr.trans (hc.gpr.trans (hb.gpr.trans ha.gpr)),
    hs.rd.trans (hc.rd.trans (hb.rd.trans ha.rd)),hs.wr.trans (hc.wr.trans (hb.wr.trans ha.wr)),
    hs.sp.trans (hc.sp.trans (hb.sp.trans ha.sp)),?_⟩
  rw [hs.mem,hc.mem,hb.mem,ha.mem,hc.gpr,hb.gpr,ha.gpr]
  have vals (j : Nat) (hj : j < 4) : c.v (vr j) =
      s₀.mem.readW (s₀.gpr .x9 + BitVec.ofNat 64 (16*j)) 128 ^^^
        s₀.mem.readW (s₀.gpr .x10 + BitVec.ofNat 64 (16*j)) 128 := by
    rw [hc.words j hj,hb.keep (vr j) (by intro k hk; exact vr_ne (by omega) (by omega) (by omega))]
    have he : a.v (vr j) = s₀.mem.readW (s₀.gpr .x9 + BitVec.ofNat 64 (16*j)) 128 := by
      simpa only [Nat.zero_add] using ha.loaded j hj hj
    rw [he,hb.loaded j hj hj,ha.mem,ha.gpr]
  simp only [writeQ4]
  rw [vals 0 (by omega),vals 1 (by omega),vals 2 (by omega),vals 3 (by omega)]
  exact writeQ4_xor _ _ _ _ _

end VG.Proof.Scrypt.AArch64.Transfer
