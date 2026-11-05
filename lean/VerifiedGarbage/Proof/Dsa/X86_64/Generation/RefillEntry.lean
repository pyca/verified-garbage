module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillABI
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.Refill
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Context
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FrameStore
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.EntryState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeometryWork
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The refillable-tape search's entry on x86-64

The entry stores the arguments in the attempts' frame and the controller's
words. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.Refill

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Impl.Bignum.X86_64 (at0)

/-- The entry's stores of registers and constants. -/
def headerA (pLen qLen : Nat) : List Instr :=
  [.store (sp 48) .rdi, .store (sp 56) .rsi, .store (Impl.Dsa.X86_64.Generation.Refill.ctl 0) .rdx,
   .store (sp 64) .rcx, .store (sp 72) .r8, .store (sp 104) .rcx, .store (sp 120) .r8,
   .store (sp 88) .rcx, .mov32 .rax (.imm 0), .store (sp 96) .rax, .store (sp 80) .rax,
   .store (sp 40) .r9,
   .mov32 .rax (.imm (BitVec.ofNat 32 pLen)), .store (sp 136) .rax,
   .mov32 .rax (.imm (BitVec.ofNat 32 qLen)), .store (sp 144) .rax, .store (sp 224) .rax]

/-- The entry's loads of `state` and `state[0]`. -/
def headerB : List Instr :=
  [.mov .rax (.mem (sp (Impl.Dsa.X86_64.Generation.Refill.frameBytes + 32 + 48 + 16))),
   .store (Impl.Dsa.X86_64.Generation.Refill.ctl 1) .rax,
   .mov .rax (.mem (at0 .rax)), .store (Impl.Dsa.X86_64.Generation.Refill.ctl 2) .rax]

theorem entryHeader_eq (pLen qLen : Nat) :
    Impl.Dsa.X86_64.Generation.Refill.entryHeader pLen qLen = headerA pLen qLen ++ headerB := rfl

/-- The memory after `headerA`. -/
def chainA (m : Mem) (F : Addr) (g : Reg → BitVec 64) (pLen qLen : Nat) : Mem :=
  ((((((((((((((m.writeW (off F 48) (g .rdi)).writeW (off F 56) (g .rsi)).writeW (off F 296) (g .rdx)).writeW
    (off F 64) (g .rcx)).writeW (off F 72) (g .r8)).writeW (off F 104) (g .rcx)).writeW (off F 120) (g .r8)).writeW
    (off F 88) (g .rcx)).writeW (off F 96) (0 : BitVec 64)).writeW (off F 80) (0 : BitVec 64)).writeW
    (off F 40) (g .r9)).writeW (off F 136) (BitVec.ofNat 64 pLen)).writeW (off F 144) (BitVec.ofNat 64 qLen)).writeW
    (off F 224) (BitVec.ofNat 64 qLen))

theorem zext_ofNat {n : Nat} (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem headerA_ok {s : State} {F : Addr} (hsp : s.gpr .rsp = F)
    (hfr : (⟨F, frameBytes⟩ : Region) ∈ s.wr) (hctl : ctlRegion F ∈ s.wr)
    (hb : F.toNat + 328 ≤ 2 ^ 64) {pLen qLen : Nat} (hp : pLen < 2 ^ 31) (hq : qLen < 2 ^ 31) :
    WP isa (.block (headerA pLen qLen)) s fun t =>
      t.mem = chainA s.mem F s.gpr pLen qLen ∧ Keep [.rax] s t := by
  have fs : Scr s F frameBytes := Scr.of_mem hfr (by unfold frameBytes; omega)
  have cs : Scr s (off F 296) 32 := Scr.of_mem hctl (by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have c0 : InRegions s.wr (off F 296) 8 := by simpa [off_off] using cs.st (d := 0) (by decide)
  refine WP.keep [.rax] ?_ rfl
  xrun [headerA, chainA, Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes,
    ea_sp, hsp, c0, fs.st (d := 48) (by decide), fs.st (d := 56) (by decide), fs.st (d := 64) (by decide),
    fs.st (d := 72) (by decide), fs.st (d := 104) (by decide), fs.st (d := 120) (by decide),
    fs.st (d := 88) (by decide), fs.st (d := 96) (by decide), fs.st (d := 80) (by decide),
    fs.st (d := 40) (by decide), fs.st (d := 136) (by decide), fs.st (d := 144) (by decide),
    fs.st (d := 224) (by decide), Nat.mul_zero, Nat.add_zero, zext_ofNat (by omega : pLen < 2 ^ 32),
    zext_ofNat (by omega : qLen < 2 ^ 32), zext_ofNat (by decide : 0 < 2 ^ 32)]
  rfl

/-! ## The controller's words -/

theorem ctl_contains (F : Addr) {k : Nat} (hk : k < 4) :
    (ctlRegion F).Contains (off F (296 + 8 * k)) 8 :=
  Offset.contains F (e := 296) (by omega) (by omega) (by omega)

theorem ctl_frame (F : Addr) :
    (ctlRegion F).Disjoint ⟨F, frameBytes⟩ :=
  (Offset.base_disjoint F (e := 296) (n := 32) (k := frameBytes) (by decide) (by omega)).symm

theorem ctl_below (F : Addr) :
    (ctlRegion F).Disjoint (below F 192) :=
  Offset.disjoint_below F (n := 192) (d := 296) (k := 32) (by omega)

theorem ctl_write (m : Mem) (F : Addr) {k : Nat} (hk : k < 4) (v : BitVec 64) :
    Frame [ctlRegion F] m (m.writeW (off F (296 + 8 * k)) v) :=
  (Frame.refl _ _).writeW (List.mem_singleton_self _) v (ctl_contains F hk)

theorem ctlWord_frame {rs : List Region} {m m' : Mem} {F : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (ctlRegion F).Disjoint r) {k : Nat} (hk : k < 4) :
    ctlWord m' F k = ctlWord m F k :=
  hf.readW (ctl_contains F hk) hd (by decide)

theorem ctlWord_write_self (m : Mem) (F : Addr) (k : Nat) (v : BitVec 64) :
    ctlWord (m.writeW (off F (296 + 8 * k)) v) F k = v := Mem.readW_writeW_self64 ..

theorem ctlWord_write_other (m : Mem) (F : Addr) {j k : Nat} (hj : j < 4)
    (hk : k < 4) (hne : j ≠ k) (v : BitVec 64) :
    ctlWord (m.writeW (off F (296 + 8 * k)) v) F j = ctlWord m F j := by
  unfold ctlWord
  rw [Mem.readW_writeW_sep (Offset.sep F (d := 296 + 8 * j) (n := 8) (e := 296 + 8 * k) (k := 8) (by omega)
    (by omega) (by omega)) (by decide)]

theorem rep_ctl {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep m F S V W)
    (hS : (ctlRegion F).Disjoint ⟨S, oRsa⟩) {k : Nat} (hk : k < 4) (v : BitVec 64) :
    Rep (m.writeW (off F (296 + 8 * k)) v) F S V W :=
  rep_of_disjoint_frame R (ctl_write m F hk v)
    (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact (ctl_frame F).symm)
    (fun r hr => by rcases List.mem_singleton.mp hr with rfl; exact hS.symm)

/-! ## The entry -/

/-- The frame words after `headerA`. -/
def wordsA (W : Nat → BitVec 64) (g : Reg → BitVec 64) (pLen qLen : Nat) : Nat → BitVec 64 :=
  upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd (upd W 6 (g .rdi)) 7 (g .rsi)) 8 (g .rcx)) 9 (g .r8))
    13 (g .rcx)) 15 (g .r8)) 11 (g .rcx)) 12 0) 10 0) 5 (g .r9)) 17 (BitVec.ofNat 64 pLen))
    18 (BitVec.ofNat 64 qLen)) 28 (BitVec.ofNat 64 qLen)

theorem chainA_rep {m : Mem} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64} (G : Geo F S)
    (R : Rep m F S V W) (hS : (ctlRegion F).Disjoint ⟨S, oRsa⟩)
    (g : Reg → BitVec 64) (pLen qLen : Nat) :
    Rep (chainA m F g pLen qLen) F S V (wordsA W g pLen qLen) := by
  have R2 := (R.wf G (k := 6) (by decide) (g .rdi)).wf G (k := 7) (by decide) (g .rsi)
  have R3 := rep_ctl R2 hS (k := 0) (by decide) (g .rdx)
  exact ((((((((((R3.wf G (k := 8) (by decide) _).wf
    G (k := 9) (by decide) _).wf G (k := 13) (by decide) _).wf G (k := 15) (by decide) _).wf G (k := 11) (by decide)
    _).wf G (k := 12) (by decide) _).wf G (k := 10) (by decide) _).wf G (k := 5) (by decide) _).wf
    G (k := 17) (by decide) _).wf G (k := 18) (by decide) _).wf G (k := 28) (by decide) _

theorem chainA_frame (m : Mem) (F : Addr) (g : Reg → BitVec 64) (pLen qLen : Nat) :
    Frame [⟨F, frameBytes⟩, ctlRegion F] m (chainA m F g pLen qLen) := by
  have fc : ∀ d, d + 8 ≤ frameBytes → (⟨F, frameBytes⟩ : Region).Contains (off F d) 8 := fun d hd =>
    Offset.contains_base F hd (by unfold frameBytes at hd; omega)
  unfold chainA
  refine Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW
    (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.writeW (Frame.refl _ _)
    (List.mem_cons_self ..) _ (fc 48 (by decide))) (List.mem_cons_self ..) _ (fc 56 (by decide)))
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _ (ctl_contains F (k := 0) (by decide)))
    (List.mem_cons_self ..) _ (fc 64 (by decide))) (List.mem_cons_self ..) _ (fc 72 (by decide)))
    (List.mem_cons_self ..) _ (fc 104 (by decide))) (List.mem_cons_self ..) _ (fc 120 (by decide)))
    (List.mem_cons_self ..) _ (fc 88 (by decide))) (List.mem_cons_self ..) _ (fc 96 (by decide)))
    (List.mem_cons_self ..) _ (fc 80 (by decide))) (List.mem_cons_self ..) _ (fc 40 (by decide)))
    (List.mem_cons_self ..) _ (fc 136 (by decide))) (List.mem_cons_self ..) _ (fc 144 (by decide)))
    (List.mem_cons_self ..) _ (fc 224 (by decide))

theorem ea_at0' (t : State) (b : Reg) : t.ea (at0 b) = t.gpr b := by
  simp only [State.ea, at0, BitVec.ofInt_ofNat, BitVec.add_zero]

theorem headerB_ok {s : State} {F : Addr} (hsp : s.gpr .rsp = F) (hctl : ctlRegion F ∈ s.wr)
    (hb : F.toNat + 328 ≤ 2 ^ 64) {a v : BitVec 64}
    (ha : InRegions (s.rd ++ s.wr) (off F 392) 8) (hav : s.mem.readW (off F 392) 64 = a)
    (hv : InRegions (s.rd ++ s.wr) a 8) (hvv : (s.mem.writeW (off F 304) a).readW a 64 = v) :
    WP isa (.block headerB) s fun t =>
      t.mem = (s.mem.writeW (off F 304) a).writeW (off F 312) v ∧ Keep [.rax] s t := by
  have cs : Scr s (off F 296) 32 := Scr.of_mem hctl (by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have c1 : InRegions s.wr (off F 304) 8 := by simpa [off_off] using cs.st (d := 8) (by decide)
  have c2 : InRegions s.wr (off F 312) 8 := by simpa [off_off] using cs.st (d := 16) (by decide)
  refine WP.keep [.rax] ?_ rfl
  xrun [headerB, Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes,
    ea_sp, ea_at0', hsp, c1, c2, ha, hav, hv, hvv]

end VG.Proof.Dsa.X86_64.Generation.Refill
