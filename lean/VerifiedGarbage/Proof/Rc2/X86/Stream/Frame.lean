import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Rc2.Stream
import VerifiedGarbage.Impl.Rc2.X86.Stream
import VerifiedGarbage.Proof.Rc2.X86.Key
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Verified
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Rc2.X86.Cbc.Lit
import VerifiedGarbage.Proof.Rc2.Scratch
import VerifiedGarbage.Proof.Rc2.X86.Stream.Lit
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Stream.Contract`. -/
section

section

/-!
# Streaming RC2-CBC on x86 (32-bit): copying bytes

Addresses `[x + d]` within the 32-bit address space, the bytes a copy leaves,
and the loop copying `ecx` bytes from `esi + sd` to `edx + dd` (`copy_ok`),
which every copy of `init` and the updates uses.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86 VG.X86.Wp
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_frame writeBytes_nil writeBytes_before)

/-! ## Addresses -/

theorem toNat_sw (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  simp only [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by have := x.isLt; omega)

/-- `[(x + k) + d]`, where nothing wraps around the 32-bit address space. -/
theorem addr_add {x : BitVec 32} {k d : Nat} (h : x.toNat + k + d < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 k) d = x.setWidth 64 + BitVec.ofNat 64 (k + d) := by
  simp only [addr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt (a := d) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + k) (by omega), Nat.mod_eq_of_lt (a := x.toNat + k + d) (by omega),
    Nat.mod_eq_of_lt (a := x.toNat + k + d) (by omega), Nat.mod_eq_of_lt (a := x.toNat) (by omega),
    Nat.mod_eq_of_lt (a := k + d) (by omega), Nat.mod_eq_of_lt (a := x.toNat + (k + d)) (by omega)]
  omega

/-- `[(x + j) + d]` is byte `j` from `[x + d]`. -/
theorem addr_step {x : BitVec 32} {j d : Nat} (h : x.toNat + j + d < 2 ^ 32) :
    addr (x + BitVec.ofNat 32 j) d = addr x d + BitVec.ofNat 64 j := by
  rw [VG.Proof.Rc2.X86.Stream.addr_add h, addr_eq (by omega), Offset.add_add, Nat.add_comm]

theorem toNat_add_ofNat {x : BitVec 32} {c : Nat} (h : x.toNat + c < 2 ^ 32) :
    (x + BitVec.ofNat 32 c).toNat = x.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := c) (by omega), Nat.mod_eq_of_lt h]

theorem toNat_add {x y : BitVec 32} (h : x.toNat + y.toNat < 2 ^ 32) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

/-- Each byte of a range within one of the regions. -/
theorem inBytes {rs : List Region} {R : Region} (hR : R ∈ rs) {A : Addr} {n : Nat}
    (hs : Region.Sub ⟨A, n⟩ R) (hn : n < 2 ^ 64) : ∀ i < n, InRegions rs (A + BitVec.ofNat 64 i) 1 :=
  fun i hi => ⟨R, hR, hs _ (Offset.contains_base _ (by omega) (by omega))⟩

/-! ## Bytes -/

theorem bytesAt_len (m : Mem) (p : Addr) (n : Nat) : (Spec.Rc2.bytesAt m p n).length = n := by
  simp [Spec.Rc2.bytesAt]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Rc2.bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Rc2.bytesAt m p r ++ xs := by
  simp only [Spec.Rc2.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

/-- The bytes written, read back. -/
theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) (xs : List Byte) (h : xs.length < 2 ^ 64) :
    Spec.Rc2.bytesAt (writeBytes m q xs) q xs.length = xs := by
  have := VG.Proof.Rc2.X86.Stream.bytesAt_writeBytes m q 0 xs (by omega)
  rwa [Nat.zero_add, BitVec.add_zero, show Spec.Rc2.bytesAt m q 0 = [] from rfl, List.nil_append] at this

/-! ## Instructions on bytes -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `movzx d, BYTE PTR [b + o]` -/
theorem wp_ldb {d b : Reg} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B o) 1)
    (k : ∀ s', Upd s s' d ((s.mem (addr B o)).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d ⟨b, o⟩ :: is)) s Q :=
  cons (s' := s.setReg d _) (by simp [exec, State.load8, ea_mk, hb, hin]) (k _ (Upd.setReg _ _ _))

/-- `mov BYTE PTR [b + o], r` -/
theorem wp_stb {b : Reg} {r : Reg8} {B : BitVec 32} {o : Nat} (hb : s.gpr b = B)
    (hout : InRegions s.wr (addr B o) 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine cons (s' := { s with mem := s.mem.writeW (addr B o) ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp [exec, State.store8, ea_mk, hb, hout]

end

/-! ## The copy loop -/

/-- What a copy of `n` bytes from `addr S sd` to `addr D dd`, from `s₀`, leaves. -/
structure CopyPost (s₀ : State) (S D : BitVec 32) (sd dd n : Nat) (s : State) : Prop where
  esi : s.gpr .esi = S + BitVec.ofNat 32 n
  edx : s.gpr .edx = D + BitVec.ofNat 32 n
  other : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes s₀.mem (addr D dd) (Spec.Rc2.bytesAt s₀.mem (addr S sd) n)

/-- The loop's state after `j` of the `n` bytes. -/
structure CopyI (s₀ : State) (S D : BitVec 32) (sd dd n j : Nat) (s : State) : Prop where
  j_le : j ≤ n
  esi : s.gpr .esi = S + BitVec.ofNat 32 j
  edx : s.gpr .edx = D + BitVec.ofNat 32 j
  ecx : s.gpr .ecx = BitVec.ofNat 32 (n - j)
  other : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes s₀.mem (addr D dd) ((Spec.Rc2.bytesAt s₀.mem (addr S sd) n).take j)

theorem contains_prefix (q : Addr) {j k : Nat} (h : j ≤ k) : (⟨q, k⟩ : Region).Contains q j := by
  simp [Region.Contains, h]

theorem copyI_post {s₀ s : State} {S D : BitVec 32} {sd dd n : Nat} (h : VG.Proof.Rc2.X86.Stream.CopyI s₀ S D sd dd n n s) :
    VG.Proof.Rc2.X86.Stream.CopyPost s₀ S D sd dd n s := by
  refine ⟨h.esi, h.edx, h.other, h.rd, h.wr, ?_⟩
  rw [h.mem, List.take_of_length_le (by rw [VG.Proof.Rc2.X86.Stream.bytesAt_len])]

section
variable {sd dd n : Nat} {s₀ : State} {S D : BitVec 32}
  (hn : n < 2 ^ 32) (hfs : S.toNat + sd + n ≤ 2 ^ 32) (hfd : D.toNat + dd + n ≤ 2 ^ 32)
  (hin : ∀ i < n, InRegions (s₀.rd ++ s₀.wr) (addr S sd + BitVec.ofNat 64 i) 1)
  (hout : ∀ i < n, InRegions s₀.wr (addr D dd + BitVec.ofNat 64 i) 1)
  (hd : Region.Disjoint ⟨addr S sd, n⟩ ⟨addr D dd, n⟩)
include hn hfs hfd hin hout hd

/-- One iteration, from byte `j < n`. -/
theorem copyBody_ok {j : Nat} (hj : j < n) {s : State} (h : VG.Proof.Rc2.X86.Stream.CopyI s₀ S D sd dd n j s) :
    WP isa (.block (Impl.Rc2.X86.Stream.copyBody sd dd)) s (fun s' =>
      VG.Proof.Rc2.X86.Stream.CopyI s₀ S D sd dd n (j + 1) s' ∧ s'.zf = some (decide (n - (j + 1) = 0))) := by
  have eS : addr (S + BitVec.ofNat 32 j) sd = addr S sd + BitVec.ofNat 64 j := VG.Proof.Rc2.X86.Stream.addr_step (by omega)
  have eD : addr (D + BitVec.ofNat 32 j) dd = addr D dd + BitVec.ofNat 64 j := VG.Proof.Rc2.X86.Stream.addr_step (by omega)
  have hbyte : s.mem (addr S sd + BitVec.ofNat 64 j) = s₀.mem (addr S sd + BitVec.ofNat 64 j) := by
    rw [h.mem]
    exact (writeBytes_frame s₀.mem _ _ (VG.Proof.Rc2.X86.Stream.contains_prefix (k := n) _ (by simp; omega))).bytes
      (R := ⟨addr S sd, n⟩) (by simpa using hd) (by show n ≤ 2 ^ 64; omega) hj
  simp only [Impl.Rc2.X86.Stream.copyBody, Impl.Rc2.X86.memOp]
  refine VG.Proof.Rc2.X86.Stream.wp_ldb h.esi (by rw [h.rd, h.wr, eS]; exact hin j hj) fun s₁ u₁ => ?_
  refine VG.Proof.Rc2.X86.Stream.wp_stb (B := D + BitVec.ofNat 32 j)
    (by rw [u₁.other _ (by decide)]; exact h.edx) (by rw [u₁.wr, h.wr, eD]; exact hout j hj)
    fun s₂ u₂ => ?_
  refine wp_addi fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_subi fun s₅ u₅ _ hz₅ => WP.block_nil ?_
  have g₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr => by rw [u₂.gpr]; exact u₁.other r hr
  have hecx : s₄.gpr .ecx = s.gpr .ecx := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), g₂ _ (by decide)]
  have hc : s.gpr .ecx - 1 = BitVec.ofNat 32 (n - (j + 1)) := by
    rw [h.ecx, ofNat_pred (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, ?_, fun r a b c d => ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂ _ (by decide), h.esi,
      BitVec.ofNat_add, BitVec.add_assoc]; rfl
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g₂ _ (by decide), h.edx,
      BitVec.ofNat_add, BitVec.add_assoc]; rfl
  · rw [u₅.gpr, hecx, hc]
  · rw [u₅.other _ b, u₄.other _ d, u₃.other _ c, g₂ _ a]; exact h.other r a b c d
  · rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]; exact h.rd
  · rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]; exact h.wr
  · have hj' : j < (Spec.Rc2.bytesAt s₀.mem (addr S sd) n).length := by rw [VG.Proof.Rc2.X86.Stream.bytesAt_len]; exact hj
    have hlen : (List.take j (Spec.Rc2.bytesAt s₀.mem (addr S sd) n)).length = j := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, show Reg8.al.reg = Reg.eax from rfl, u₁.gpr, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj', Option.toList_some,
      writeBytes_snoc _ _ _ _ (by rw [hlen]; omega), hlen, eD, eS, ← h.mem, hbyte,
      BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
    congr 1
    simp [Spec.Rc2.bytesAt]
  · rw [hz₅, hecx, hc, ofNat_beq_zero (by omega)]

theorem copyLoop_ok {s : State} (hpos : 0 < n) (h : VG.Proof.Rc2.X86.Stream.CopyI s₀ S D sd dd n 0 s) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Rc2.X86.Stream.CopyPost s₀ S D sd dd n s' → Q s') :
    WP isa (.loop (.block (Impl.Rc2.X86.Stream.copyBody sd dd)) .ne) s Q := by
  refine WP.loop (M := isa) (fun k (s : State) => ∃ j, k = n - j ∧ j < n ∧ VG.Proof.Rc2.X86.Stream.CopyI s₀ S D sd dd n j s) ?_ n s
    ⟨0, by omega, hpos, h⟩
  rintro k s ⟨j, rfl, hj, h⟩
  refine (VG.Proof.Rc2.X86.Stream.copyBody_ok hn hfs hfd hin hout hd hj h).mono fun s' ⟨h', hz⟩ => ?_
  by_cases hjn : j + 1 = n
  · refine .inl ⟨?_, hQ _ (VG.Proof.Rc2.X86.Stream.copyI_post (hjn ▸ h'))⟩
    simp only [eval, hz, show n - (j + 1) = 0 by omega, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, n - (j + 1), by omega, j + 1, rfl, by omega, h'⟩
    simp only [eval, hz, show n - (j + 1) ≠ 0 by omega, decide_false, Option.map_some, Bool.not_false]

/-- The copy of `ecx = n` bytes from `esi = S` (`[esi + sd]`) to `edx = D`
(`[edx + dd]`). -/
theorem copy_ok (hS : s₀.gpr .esi = S) (hD : s₀.gpr .edx = D) (hC : s₀.gpr .ecx = BitVec.ofNat 32 n)
    {Q : State → Prop} (hQ : ∀ s', VG.Proof.Rc2.X86.Stream.CopyPost s₀ S D sd dd n s' → Q s') :
    WP isa (Impl.Rc2.X86.Stream.copy sd dd) s₀ Q := by
  refine WP.seq (wp_test fun s₁ f₁ hz₁ => WP.block_nil ?_)
  have hz : s₁.zf = some (decide (n = 0)) := by
    rw [hz₁, hC, BitVec.and_self, ofNat_beq_zero hn]
  refine WP.ite _ hz (fun h0 => WP.block_nil ?_) (fun h0 => ?_)
  · have h0 : n = 0 := by simpa using h0
    subst h0
    refine hQ _ ⟨?_, ?_, fun r _ _ _ _ => by rw [f₁.gpr], f₁.rd, f₁.wr, ?_⟩
    · rw [f₁.gpr, hS]; simp
    · rw [f₁.gpr, hD]; simp
    · rw [f₁.mem]; simp [Spec.Rc2.bytesAt, writeBytes_nil]
  · have hpos : 0 < n := by simp at h0; omega
    exact VG.Proof.Rc2.X86.Stream.copyLoop_ok hn hfs hfd hin hout hd hpos
      ⟨by omega, by rw [f₁.gpr, hS]; simp, by rw [f₁.gpr, hD]; simp, by rw [f₁.gpr, hC]; simp,
        fun r _ _ _ _ => by rw [f₁.gpr], f₁.rd, f₁.wr, by rw [f₁.mem]; simp [writeBytes_nil]⟩ hQ

end

end VG.Proof.Rc2.X86.Stream

end

/-!
# Streaming RC2-CBC on x86 (32-bit): the contracts the proofs use

`Spec.Rc2.cbcInitContract` and `Spec.Rc2.cbcUpdateContract` spelled out for
x86, with the arguments only read (the taint analysis follows them in memory
only while nothing that may alias them is written): `Verified.lean` moves the
proofs to the shared contracts, which let the code write them.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

def initContract : Contract isa where
  pre s :=
    let key : Region := ⟨(VG.X86.arg s 0).setWidth 64, (VG.X86.arg s 1).toNat⟩
    let iv : Region := ⟨(VG.X86.arg s 3).setWidth 64, (VG.X86.arg s 4).toNat⟩
    let ctx : Region := ⟨(VG.X86.arg s 5).setWidth 64, 144⟩
    let buf : Region := ⟨(VG.X86.arg s 6).setWidth 64, 576⟩
    let args : Region := ⟨VG.X86.argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) 24
    s.rd = [key, iv, args] ∧ s.wr = [ctx, buf] ∧
      key.Disjoint ctx ∧ key.Disjoint buf ∧ iv.Disjoint ctx ∧ iv.Disjoint buf ∧ ctx.Disjoint buf ∧
      args.Disjoint ctx ∧ args.Disjoint buf ∧ ret.Disjoint ctx ∧ ret.Disjoint buf ∧
      stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint ctx ∧ stack.Disjoint buf ∧
      (VG.X86.arg s 0).toNat + (VG.X86.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 3).toNat + (VG.X86.arg s 4).toNat ≤ 2 ^ 32 ∧
      (VG.X86.arg s 5).toNat + 144 ≤ 2 ^ 32 ∧ (VG.X86.arg s 6).toNat + 576 ≤ 2 ^ 32 ∧
      24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32
  post s s' :=
    ∀ direction, match Spec.Rc2.initWithEffectiveBits
        (Spec.Rc2.bytesAt s.mem ((VG.X86.arg s 0).setWidth 64) (VG.X86.arg s 1).toNat)
        (Spec.Rc2.bytesAt s.mem ((VG.X86.arg s 3).setWidth 64) (VG.X86.arg s 4).toNat) direction (VG.X86.arg s 2).toNat with
      | .ok c => BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax) = 0 ∧ Spec.Rc2.contextAt s'.mem ((VG.X86.arg s 5).setWidth 64) direction 0 = c
      | .error e => (BitVec.setWidth 32 (s'.gpr .edx ++ s'.gpr .eax)).toNat = e.code
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, VG.X86.arg s₁ i = VG.X86.arg s₂ i

def updateContract (d : Spec.Rc2.Direction) : Contract isa where
  pre s :=
    let ctx : Region := ⟨(VG.X86.arg s 0).setWidth 64, 144⟩
    let data : Region := ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩
    let out : Region := ⟨(VG.X86.arg s 4).setWidth 64, (VG.X86.arg s 5).toNat⟩
    let buf : Region := ⟨(VG.X86.arg s 6).setWidth 64, 576⟩
    let args : Region := ⟨VG.X86.argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack := below (s.gpr .esp) 40
    s.rd = [data, args] ∧ s.wr = [ctx, out, buf] ∧
      ctx.Disjoint data ∧ ctx.Disjoint out ∧ ctx.Disjoint buf ∧ data.Disjoint out ∧
      data.Disjoint buf ∧ out.Disjoint buf ∧
      args.Disjoint ctx ∧ args.Disjoint out ∧ args.Disjoint buf ∧
      ret.Disjoint ctx ∧ ret.Disjoint out ∧ ret.Disjoint buf ∧
      stack.Disjoint ctx ∧ stack.Disjoint data ∧ stack.Disjoint out ∧ stack.Disjoint buf ∧
      (VG.X86.arg s 0).toNat + 144 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧
      (VG.X86.arg s 4).toNat + (VG.X86.arg s 5).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 6).toNat + 576 ≤ 2 ^ 32 ∧
      40 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 ∧
      (VG.X86.arg s 1).toNat < 8 ∧ (VG.X86.arg s 5).toNat = ((VG.X86.arg s 1).toNat + (VG.X86.arg s 3).toNat) / 8 * 8
  post s s' :=
    let result := Spec.Rc2.update (Spec.Rc2.contextAt s.mem ((VG.X86.arg s 0).setWidth 64) d (VG.X86.arg s 1).toNat)
      (Spec.Rc2.bytesAt s.mem ((VG.X86.arg s 2).setWidth 64) (VG.X86.arg s 3).toNat)
    Spec.Rc2.contextAt s'.mem ((VG.X86.arg s 0).setWidth 64) d (((VG.X86.arg s 1).toNat + (VG.X86.arg s 3).toNat) % 8) =
        result.1 ∧
      Spec.Rc2.bytesAt s'.mem ((VG.X86.arg s 4).setWidth 64) (VG.X86.arg s 5).toNat = result.2
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, VG.X86.arg s₁ i = VG.X86.arg s₂ i

end VG.Proof.Rc2.X86.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Stream.InitCorrect`. -/
section

section

/-!
# Streaming RC2-CBC on x86 (32-bit): `init` before the call

Names for the arguments and regions of `init` (`Pre`), the length checks
(`checks_ok`), and the copy of the IV and the arguments of the key expansion
(`initArgs_ok`).
-/

namespace VG.Proof.Rc2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

theorem ofNat_toNat (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev key : BitVec 32 := VG.X86.arg s₀ 0
abbrev kl : Nat := (VG.X86.arg s₀ 1).toNat
abbrev eb : Nat := (VG.X86.arg s₀ 2).toNat
abbrev iv : BitVec 32 := VG.X86.arg s₀ 3
abbrev il : Nat := (VG.X86.arg s₀ 4).toNat
abbrev ctx : BitVec 32 := VG.X86.arg s₀ 5
abbrev scr : BitVec 32 := VG.X86.arg s₀ 6
abbrev kA : Addr := (VG.Proof.Rc2.X86.Stream.Init.key s₀).setWidth 64
abbrev ivA : Addr := (VG.Proof.Rc2.X86.Stream.Init.iv s₀).setWidth 64
abbrev cA : Addr := (VG.Proof.Rc2.X86.Stream.Init.ctx s₀).setWidth 64
abbrev sA : Addr := (VG.Proof.Rc2.X86.Stream.Init.scr s₀).setWidth 64
abbrev keyR : Region := ⟨VG.Proof.Rc2.X86.Stream.Init.kA s₀, VG.Proof.Rc2.X86.Stream.Init.kl s₀⟩
abbrev ivR : Region := ⟨VG.Proof.Rc2.X86.Stream.Init.ivA s₀, VG.Proof.Rc2.X86.Stream.Init.il s₀⟩
abbrev ctxR : Region := ⟨VG.Proof.Rc2.X86.Stream.Init.cA s₀, 144⟩
abbrev scR : Region := ⟨VG.Proof.Rc2.X86.Stream.Init.sA s₀, 576⟩
abbrev argR : Region := ⟨VG.X86.argAddr s₀ 0, 28⟩
abbrev retR : Region := ⟨(VG.Proof.Rc2.X86.Stream.Init.E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (VG.Proof.Rc2.X86.Stream.Init.E s₀) 24
/-- Where the chaining value goes. -/
abbrev cvR : Region := ⟨VG.Proof.Rc2.X86.Stream.Init.cA s₀ + BitVec.ofNat 64 128, 8⟩
abbrev schR : Region := ⟨VG.Proof.Rc2.X86.Stream.Init.cA s₀, 128⟩

/-- The value `init` returns. -/
def code : Nat :=
  if ¬(1 ≤ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ≤ 128) then 1 else if ¬(1 ≤ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ≤ 1024) then 2
  else if VG.Proof.Rc2.X86.Stream.Init.il s₀ ≠ 8 then 3 else 0

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Rc2.X86.Stream.Init.keyR s₀, VG.Proof.Rc2.X86.Stream.Init.ivR s₀, VG.Proof.Rc2.X86.Stream.Init.argR s₀]
  wr : s₀.wr = [VG.Proof.Rc2.X86.Stream.Init.ctxR s₀, VG.Proof.Rc2.X86.Stream.Init.scR s₀]
  k_c : (VG.Proof.Rc2.X86.Stream.Init.keyR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Init.ctxR s₀)
  k_s : (VG.Proof.Rc2.X86.Stream.Init.keyR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Init.scR s₀)
  i_c : (VG.Proof.Rc2.X86.Stream.Init.ivR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Init.ctxR s₀)
  i_s : (VG.Proof.Rc2.X86.Stream.Init.ivR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Init.scR s₀)
  c_s : (VG.Proof.Rc2.X86.Stream.Init.ctxR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Init.scR s₀)
  a_c : (VG.Proof.Rc2.X86.Stream.Init.argR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Init.ctxR s₀)
  a_s : (VG.Proof.Rc2.X86.Stream.Init.argR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Init.scR s₀)
  r_c : (VG.Proof.Rc2.X86.Stream.Init.retR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Init.ctxR s₀)
  r_s : (VG.Proof.Rc2.X86.Stream.Init.retR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Init.scR s₀)
  t_k : (VG.Proof.Rc2.X86.Stream.Init.stkR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Init.keyR s₀)
  t_i : (VG.Proof.Rc2.X86.Stream.Init.stkR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Init.ivR s₀)
  t_c : (VG.Proof.Rc2.X86.Stream.Init.stkR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Init.ctxR s₀)
  t_s : (VG.Proof.Rc2.X86.Stream.Init.stkR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Init.scR s₀)
  k_fit : (VG.Proof.Rc2.X86.Stream.Init.key s₀).toNat + VG.Proof.Rc2.X86.Stream.Init.kl s₀ ≤ 2 ^ 32
  i_fit : (VG.Proof.Rc2.X86.Stream.Init.iv s₀).toNat + VG.Proof.Rc2.X86.Stream.Init.il s₀ ≤ 2 ^ 32
  c_fit : (VG.Proof.Rc2.X86.Stream.Init.ctx s₀).toNat + 144 ≤ 2 ^ 32
  s_fit : (VG.Proof.Rc2.X86.Stream.Init.scr s₀).toNat + 576 ≤ 2 ^ 32
  sp_lo : 24 ≤ (VG.Proof.Rc2.X86.Stream.Init.E s₀).toNat
  sp_fit : (VG.Proof.Rc2.X86.Stream.Init.E s₀).toNat + 32 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : initContract.pre s₀) : VG.Proof.Rc2.X86.Stream.Init.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩

theorem cv_sub {s₀ : State} : Region.Sub (VG.Proof.Rc2.X86.Stream.Init.cvR s₀) (VG.Proof.Rc2.X86.Stream.Init.ctxR s₀) := Offset.sub_base _ (by decide)
theorem sch_sub {s₀ : State} : Region.Sub (VG.Proof.Rc2.X86.Stream.Init.schR s₀) (VG.Proof.Rc2.X86.Stream.Init.ctxR s₀) := Region.sub_prefix (by decide)
theorem sch_cv {s₀ : State} : (VG.Proof.Rc2.X86.Stream.Init.schR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Init.cvR s₀) := Offset.base_disjoint _ (by decide) (by decide)

namespace Pre
variable {s₀ : State} (hp : VG.Proof.Rc2.X86.Stream.Init.Pre s₀)
include hp

theorem argAddr_eq (i : Nat) (hi : i < 7) :
    addr (VG.Proof.Rc2.X86.Stream.Init.E s₀) (4 + 4 * i) = (VG.Proof.Rc2.X86.Stream.Init.E s₀).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) := by
  have := hp.sp_fit; exact addr_eq (by omega)

theorem arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨addr (VG.Proof.Rc2.X86.Stream.Init.E s₀) (4 + 4 * i), 4⟩ (VG.Proof.Rc2.X86.Stream.Init.argR s₀) := by
  show Region.Sub _ ⟨addr (VG.Proof.Rc2.X86.Stream.Init.E s₀) (4 + 4 * 0), 28⟩
  rw [hp.argAddr_eq i hi, hp.argAddr_eq 0 (by decide)]
  exact Offset.sub _ (by omega) (by omega)

theorem rin {s : State} (hrd : s.rd = s₀.rd) {i : Nat} (hi : i < 7) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Rc2.X86.Stream.Init.E s₀) (4 + 4 * i)) 4 := by
  refine ⟨VG.Proof.Rc2.X86.Stream.Init.argR s₀, by simp [hrd, hp.rd], ?_⟩
  show (⟨addr (VG.Proof.Rc2.X86.Stream.Init.E s₀) (4 + 4 * 0), 28⟩ : Region).Contains _ _
  rw [hp.argAddr_eq i hi, hp.argAddr_eq 0 (by decide)]
  exact Offset.contains _ (by omega) (by omega) (by have := hp.sp_fit; omega)

theorem scr_addr {d : Nat} (hd : d + 4 ≤ 576) : addr (VG.Proof.Rc2.X86.Stream.Init.scr s₀) d = VG.Proof.Rc2.X86.Stream.Init.sA s₀ + BitVec.ofNat 64 d := by
  have := hp.s_fit; exact addr_eq (by omega)

theorem scr_sub {d : Nat} (hd : d + 4 ≤ 576) : Region.Sub ⟨addr (VG.Proof.Rc2.X86.Stream.Init.scr s₀) d, 4⟩ (VG.Proof.Rc2.X86.Stream.Init.scR s₀) := by
  rw [hp.scr_addr hd]; exact Offset.sub_base _ hd

theorem ctx_addr {d : Nat} (hd : d + 4 ≤ 144) : addr (VG.Proof.Rc2.X86.Stream.Init.ctx s₀) d = VG.Proof.Rc2.X86.Stream.Init.cA s₀ + BitVec.ofNat 64 d := by
  have := hp.c_fit; exact addr_eq (by omega)

end Pre

/-- What holds before the call. -/
structure Common (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = VG.Proof.Rc2.X86.Stream.Init.E s₀
  edi : s.gpr .edi = s₀.gpr .edi
  ebp : s.gpr .ebp = s₀.gpr .ebp
  frame : Frame [VG.Proof.Rc2.X86.Stream.Init.cvR s₀, VG.Proof.Rc2.X86.Stream.Init.scR s₀] s₀.mem s.mem

theorem Common.refl (s₀ : State) : VG.Proof.Rc2.X86.Stream.Init.Common s₀ s₀ := ⟨rfl, rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Common.upd {s₀ s s' : State} (h : VG.Proof.Rc2.X86.Stream.Init.Common s₀ s) {d : Reg} {v : BitVec 32} (u : Upd s s' d v)
    (h₁ : d ≠ .esp) (h₂ : d ≠ .edi) (h₃ : d ≠ .ebp) : VG.Proof.Rc2.X86.Stream.Init.Common s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, (u.other _ (Ne.symm h₁)).trans h.esp,
    (u.other _ (Ne.symm h₂)).trans h.edi, (u.other _ (Ne.symm h₃)).trans h.ebp,
    by rw [u.mem]; exact h.frame⟩

theorem Common.fupd {s₀ s s' : State} (h : VG.Proof.Rc2.X86.Stream.Init.Common s₀ s) (u : Fupd s s') : VG.Proof.Rc2.X86.Stream.Init.Common s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, by rw [u.gpr]; exact h.esp, by rw [u.gpr]; exact h.edi,
    by rw [u.gpr]; exact h.ebp, by rw [u.mem]; exact h.frame⟩

theorem Common.arg {s₀ s : State} (hp : VG.Proof.Rc2.X86.Stream.Init.Pre s₀) (h : VG.Proof.Rc2.X86.Stream.Init.Common s₀ s) {i : Nat} (hi : i < 7) :
    s.mem.readW (addr (VG.Proof.Rc2.X86.Stream.Init.E s₀) (4 + 4 * i)) 32 = VG.X86.arg s₀ i := by
  have hs := hp.arg_sub hi
  refine (h.frame.readW (Region.contains_self _ _) ?_ (by decide)).trans rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact (hp.a_c.sub_right VG.Proof.Rc2.X86.Stream.Init.cv_sub).sub_left hs
  · exact hp.a_s.sub_left hs

theorem wp_arg {s₀ s : State} (hp : VG.Proof.Rc2.X86.Stream.Init.Pre s₀) (h : VG.Proof.Rc2.X86.Stream.Init.Common s₀ s) {i : Nat} (hi : i < 7) {d : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (VG.X86.arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (Impl.Rc2.X86.Stream.argOp i)) :: is)) s Q :=
  wp_ldm (b := .esp) (o := 4 + 4 * i) h.esp (hp.rin h.rd hi) fun s' u => k s' (h.arg hp hi ▸ u)

/-! ## The checks -/

theorem pred_lt (x : BitVec 32) {n : Nat} (hn : n < 2 ^ 32) :
    decide ((x - BitVec.ofNat 32 1).toNat < n) = decide (1 ≤ x.toNat ∧ x.toNat ≤ n) := by
  rw [decide_eq_decide, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem checks_ok {s₀ : State} (hp : VG.Proof.Rc2.X86.Stream.Init.Pre s₀) {Q : State → Prop}
    (hQ : ∀ t, VG.Proof.Rc2.X86.Stream.Init.Common s₀ t → t.mem = s₀.mem → t.gpr .eax = BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Init.code s₀) →
      t.gpr .ebx = s₀.gpr .ebx → t.gpr .esi = s₀.gpr .esi → Q t) :
    WP isa checks s₀ Q := by
  have c₀ := Common.refl s₀
  rw [checks]
  refine WP.seq ?_
  refine wp_movi fun s₁ u₁ => ?_
  have c₁ := c₀.upd u₁ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Init.wp_arg hp c₁ (i := 1) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine wp_subi fun s₃ u₃ _ _ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_cmpi fun s₄ f₄ cf₄ _ => WP.block_nil ?_
  have c₄ := c₃.fupd f₄
  have k₄ : decide (1 ≤ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ≤ 128) = decide ((s₃.gpr .ecx).toNat < (128 : BitVec 32).toNat) := by
    rw [u₃.gpr, u₂.gpr]; exact (VG.Proof.Rc2.X86.Stream.Init.pred_lt _ (by decide)).symm
  have m₄ : s₄.mem = s₀.mem := by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g₄ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) : s₄.gpr r = s₀.gpr r := by
    rw [f₄.gpr, u₃.other _ h₂, u₂.other _ h₂, u₁.other _ h₁]
  have a₄ : s₄.gpr .eax = BitVec.ofNat 32 1 := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  refine WP.ite (!decide (1 ≤ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ≤ 128)) (by
    show s₄.cf.map (!·) = _; rw [cf₄, ← k₄]; rfl) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hk : ¬(1 ≤ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ≤ 128) := of_decide_eq_false (by revert hb; cases decide (1 ≤ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ≤ 128) <;> simp)
    refine hQ s₄ c₄ m₄ (by rw [a₄, VG.Proof.Rc2.X86.Stream.Init.code, ite_eq_left_of_eq_true _ _ (eq_true hk)]) (g₄ _ (by decide) (by decide))
      (g₄ _ (by decide) (by decide))
  have hk : 1 ≤ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ≤ 128 := of_decide_eq_true (by revert hb; cases decide (1 ≤ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ≤ 128) <;> simp)
  -- `effective_bits`.
  refine WP.seq ?_
  refine wp_movi fun s₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Init.wp_arg hp c₅ (i := 2) (by decide) fun s₆ u₆ => ?_
  have c₆ := c₅.upd u₆ (by decide) (by decide) (by decide)
  refine wp_subi fun s₇ u₇ _ _ => ?_
  have c₇ := c₆.upd u₇ (by decide) (by decide) (by decide)
  refine wp_cmpi fun s₈ f₈ cf₈ _ => WP.block_nil ?_
  have c₈ := c₇.fupd f₈
  have k₈ : decide (1 ≤ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ≤ 1024) = decide ((s₇.gpr .ecx).toNat < (1024 : BitVec 32).toNat) := by
    rw [u₇.gpr, u₆.gpr]; exact (VG.Proof.Rc2.X86.Stream.Init.pred_lt _ (by decide)).symm
  have m₈ : s₈.mem = s₀.mem := by rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄]
  have g₈ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) : s₈.gpr r = s₀.gpr r := by
    rw [f₈.gpr, u₇.other _ h₂, u₆.other _ h₂, u₅.other _ h₁, g₄ _ h₁ h₂]
  have a₈ : s₈.gpr .eax = BitVec.ofNat 32 2 := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  refine WP.ite (!decide (1 ≤ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ≤ 1024)) (by
    show s₈.cf.map (!·) = _; rw [cf₈, ← k₈]; rfl) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have he : ¬(1 ≤ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ≤ 1024) := of_decide_eq_false (by revert hb; cases decide (1 ≤ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ≤ 1024) <;> simp)
    refine hQ s₈ c₈ m₈ (by rw [a₈, VG.Proof.Rc2.X86.Stream.Init.code, ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hk)), ite_eq_left_of_eq_true _ _ (eq_true he)]) (g₈ _ (by decide) (by decide)) (g₈ _ (by decide) (by decide))
  have he : 1 ≤ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ≤ 1024 := of_decide_eq_true (by revert hb; cases decide (1 ≤ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ≤ 1024) <;> simp)
  -- `iv_len`.
  refine WP.seq ?_
  refine wp_movi fun s₉ u₉ => ?_
  have c₉ := c₈.upd u₉ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Init.wp_arg hp c₉ (i := 4) (by decide) fun s₁₀ u₁₀ => ?_
  have c₁₀ := c₉.upd u₁₀ (by decide) (by decide) (by decide)
  refine wp_cmpi fun s₁₁ f₁₁ _ zf₁₁ => WP.block_nil ?_
  have c₁₁ := c₁₀.fupd f₁₁
  have m₁₁ : s₁₁.mem = s₀.mem := by rw [f₁₁.mem, u₁₀.mem, u₉.mem, m₈]
  have g₁₁ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) : s₁₁.gpr r = s₀.gpr r := by
    rw [f₁₁.gpr, u₁₀.other _ h₂, u₉.other _ h₁, g₈ _ h₁ h₂]
  have z : (s₁₀.gpr .ecx - 8 == 0) = decide (VG.Proof.Rc2.X86.Stream.Init.il s₀ = 8) := by
    rw [u₁₀.gpr, ← VG.Proof.Rc2.X86.Stream.Init.ofNat_toNat (VG.X86.arg s₀ 4)]
    exact sub_beq (VG.X86.arg s₀ 4).isLt (by decide)
  refine WP.ite (!decide (VG.Proof.Rc2.X86.Stream.Init.il s₀ = 8)) (by
    show s₁₁.zf.map (!·) = _; rw [zf₁₁, z]; rfl) (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · have hi : VG.Proof.Rc2.X86.Stream.Init.il s₀ ≠ 8 := of_decide_eq_false (by revert hb; cases decide (VG.Proof.Rc2.X86.Stream.Init.il s₀ = 8) <;> simp)
    refine hQ s₁₁ c₁₁ m₁₁ ?_ (g₁₁ _ (by decide) (by decide)) (g₁₁ _ (by decide) (by decide))
    rw [f₁₁.gpr, u₁₀.other _ (by decide), u₉.gpr]
    rw [VG.Proof.Rc2.X86.Stream.Init.code, ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hk)), ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro he)), ite_eq_left_of_eq_true _ _ (eq_true hi)]
  · have hi : VG.Proof.Rc2.X86.Stream.Init.il s₀ = 8 := of_decide_eq_true (by revert hb; cases decide (VG.Proof.Rc2.X86.Stream.Init.il s₀ = 8) <;> simp)
    refine wp_movi fun s₁₂ u₁₂ => WP.block_nil ?_
    refine hQ s₁₂ (c₁₁.upd u₁₂ (by decide) (by decide) (by decide)) (by rw [u₁₂.mem, m₁₁]) ?_
      (by rw [u₁₂.other _ (by decide)]; exact g₁₁ _ (by decide) (by decide))
      (by rw [u₁₂.other _ (by decide)]; exact g₁₁ _ (by decide) (by decide))
    rw [u₁₂.gpr]
    rw [VG.Proof.Rc2.X86.Stream.Init.code, ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hk)), ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro he)), ite_eq_right_of_eq_false _ _ (eq_false (not_not_intro hi))]

end VG.Proof.Rc2.X86.Stream.Init

end

section

/-!
# Streaming RC2-CBC on x86 (32-bit): the IV and the key expansion's arguments

With valid lengths, `init` copies the IV to `ctx + 128`, saves our caller's
`ebx` and `esi` in `scratch[512..520)`, and loads the arguments of
`vg_rc2_expand_key` (`initArgs_ok`).
-/

namespace VG.Proof.Rc2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

/-- `Common` after a store within the chaining value or the scratch space. -/
theorem Common.store {s₀ s s' : State} (h : VG.Proof.Rc2.X86.Stream.Init.Common s₀ s) {a : Addr} {v : BitVec 32}
    (u : Mupd s s' (s.mem.writeW a v)) {r : Region} (hr : r ∈ [VG.Proof.Rc2.X86.Stream.Init.cvR s₀, VG.Proof.Rc2.X86.Stream.Init.scR s₀]) (ha : r.Contains a 4) :
    VG.Proof.Rc2.X86.Stream.Init.Common s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, by rw [u.gpr]; exact h.esp, by rw [u.gpr]; exact h.edi,
    by rw [u.gpr]; exact h.ebp, by rw [u.mem]; exact h.frame.writeW hr _ ha⟩

theorem initArgs_ok {s₀ s : State} (hp : VG.Proof.Rc2.X86.Stream.Init.Pre s₀) (hi : VG.Proof.Rc2.X86.Stream.Init.il s₀ = 8) (hc : VG.Proof.Rc2.X86.Stream.Init.Common s₀ s) (hm : s.mem = s₀.mem)
    (hb : s.gpr .ebx = s₀.gpr .ebx) (hs : s.gpr .esi = s₀.gpr .esi) {Q : State → Prop}
    (hQ : ∀ t, VG.Proof.Rc2.X86.Stream.Init.Common s₀ t → t.gpr .eax = VG.Proof.Rc2.X86.Stream.Init.key s₀ → t.gpr .ecx = VG.X86.arg s₀ 1 → t.gpr .edx = VG.X86.arg s₀ 2 →
      t.gpr .esi = VG.Proof.Rc2.X86.Stream.Init.ctx s₀ → t.gpr .ebx = VG.Proof.Rc2.X86.Stream.Init.scr s₀ →
      Spec.Rc2.blockAt t.mem (VG.Proof.Rc2.X86.Stream.Init.cA s₀ + BitVec.ofNat 64 128) = Spec.Rc2.blockAt s₀.mem (VG.Proof.Rc2.X86.Stream.Init.ivA s₀) →
      t.mem.readW (addr (VG.Proof.Rc2.X86.Stream.Init.scr s₀) 512) 32 = s₀.gpr .ebx → t.mem.readW (addr (VG.Proof.Rc2.X86.Stream.Init.scr s₀) 516) 32 = s₀.gpr .esi →
      Q t) :
    WP isa (.block initArgs) s Q := by
  have hif := hp.i_fit
  have hcf := hp.c_fit
  have iv4 : addr (VG.Proof.Rc2.X86.Stream.Init.iv s₀) 4 = VG.Proof.Rc2.X86.Stream.Init.ivA s₀ + BitVec.ofNat 64 4 := addr_eq (by omega)
  have c128 : addr (VG.Proof.Rc2.X86.Stream.Init.ctx s₀) 128 = VG.Proof.Rc2.X86.Stream.Init.cA s₀ + BitVec.ofNat 64 128 := hp.ctx_addr (by decide)
  have c132 : addr (VG.Proof.Rc2.X86.Stream.Init.ctx s₀) 132 = VG.Proof.Rc2.X86.Stream.Init.cA s₀ + BitVec.ofNat 64 132 := hp.ctx_addr (by decide)
  have ivIn₀ : InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Rc2.X86.Stream.Init.iv s₀) 0) 4 := by
    rw [addr_eq (by have := (VG.Proof.Rc2.X86.Stream.Init.iv s₀).isLt; omega)]
    exact ⟨VG.Proof.Rc2.X86.Stream.Init.ivR s₀, by simp [hp.rd], Offset.contains_base _ (by omega) (by omega)⟩
  have ivIn₄ : InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Rc2.X86.Stream.Init.iv s₀) 4) 4 := by
    rw [iv4]; exact ⟨VG.Proof.Rc2.X86.Stream.Init.ivR s₀, by simp [hp.rd], Offset.contains_base _ (by omega) (by omega)⟩
  have iv0 : addr (VG.Proof.Rc2.X86.Stream.Init.iv s₀) 0 = VG.Proof.Rc2.X86.Stream.Init.ivA s₀ := by
    rw [addr_eq (by have := (VG.Proof.Rc2.X86.Stream.Init.iv s₀).isLt; omega)]; exact BitVec.add_zero _
  have cvC (d : Nat) (hd : 128 ≤ d) (hd' : d + 4 ≤ 136) : (VG.Proof.Rc2.X86.Stream.Init.cvR s₀).Contains (VG.Proof.Rc2.X86.Stream.Init.cA s₀ + BitVec.ofNat 64 d) 4 :=
    Offset.contains _ hd (by omega) (by omega)
  have cvIn (d : Nat) (hd : 128 ≤ d) (hd' : d + 4 ≤ 136) : InRegions s₀.wr (VG.Proof.Rc2.X86.Stream.Init.cA s₀ + BitVec.ofNat 64 d) 4 :=
    ⟨VG.Proof.Rc2.X86.Stream.Init.ctxR s₀, by simp [hp.wr], Offset.contains_base _ (by omega) (by omega)⟩
  have scC (d : Nat) (hd : d + 4 ≤ 576) : (VG.Proof.Rc2.X86.Stream.Init.scR s₀).Contains (addr (VG.Proof.Rc2.X86.Stream.Init.scr s₀) d) 4 := by
    rw [hp.scr_addr hd]; exact Offset.contains_base _ hd (by omega)
  have scIn (d : Nat) (hd : d + 4 ≤ 576) : InRegions s₀.wr (addr (VG.Proof.Rc2.X86.Stream.Init.scr s₀) d) 4 :=
    ⟨VG.Proof.Rc2.X86.Stream.Init.scR s₀, by simp [hp.wr], scC d hd⟩
  simp only [initArgs, save, List.cons_append, List.nil_append]
  refine VG.Proof.Rc2.X86.Stream.Init.wp_arg hp hc (i := 3) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Init.wp_arg hp c₁ (i := 5) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  have eax₂ : s₂.gpr .eax = VG.Proof.Rc2.X86.Stream.Init.iv s₀ := by rw [u₂.other _ (by decide)]; exact u₁.gpr
  refine wp_ldm (o := 0) eax₂ (by rw [c₂.rd, c₂.wr]; exact ivIn₀) fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_stm (o := 128) (B := VG.Proof.Rc2.X86.Stream.Init.ctx s₀) (by rw [u₃.other _ (by decide)]; exact u₂.gpr)
    (by rw [u₃.wr, c₂.wr, c128]; exact cvIn 128 (by decide) (by decide)) fun s₄ u₄ => ?_
  have c₄ := c₃.store u₄ (r := VG.Proof.Rc2.X86.Stream.Init.cvR s₀) (by simp) (by rw [c128]; exact cvC 128 (by decide) (by decide))
  refine wp_ldm (o := 4) (B := VG.Proof.Rc2.X86.Stream.Init.iv s₀) (by rw [u₄.gpr, u₃.other _ (by decide)]; exact eax₂)
    (by rw [c₄.rd, c₄.wr]; exact ivIn₄) fun s₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide) (by decide) (by decide)
  refine wp_stm (o := 132) (B := VG.Proof.Rc2.X86.Stream.Init.ctx s₀) (by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide)]; exact u₂.gpr)
    (by rw [u₅.wr, c₄.wr, c132]; exact cvIn 132 (by decide) (by decide)) fun s₆ u₆ => ?_
  have c₆ := c₅.store u₆ (r := VG.Proof.Rc2.X86.Stream.Init.cvR s₀) (by simp) (by rw [c132]; exact cvC 132 (by decide) (by decide))
  -- The chaining value.
  have m₆ : s₆.mem = s₀.mem.writeW (VG.Proof.Rc2.X86.Stream.Init.cA s₀ + BitVec.ofNat 64 128) (s₀.mem.readW (VG.Proof.Rc2.X86.Stream.Init.ivA s₀) 64) := by
    have r₄ : s₄.mem.readW (VG.Proof.Rc2.X86.Stream.Init.ivA s₀ + BitVec.ofNat 64 4) 32 = s₀.mem.readW (VG.Proof.Rc2.X86.Stream.Init.ivA s₀ + BitVec.ofNat 64 4) 32 := by
      rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem, hm, c128]
      refine Mem.readW_writeW_sep (Region.Disjoint.sep (hp.i_c.sub_right VG.Proof.Rc2.X86.Stream.Init.cv_sub) ?_ ?_) (by decide)
      · exact Offset.contains_base _ (by omega) (by omega)
      · exact VG.Proof.Rc2.X86.Stream.contains_prefix _ (by decide)
    have m₄ : s₄.mem = s₀.mem.writeW (VG.Proof.Rc2.X86.Stream.Init.cA s₀ + BitVec.ofNat 64 128) (s₀.mem.readW (VG.Proof.Rc2.X86.Stream.Init.ivA s₀) 32) := by
      rw [u₄.mem, u₃.gpr, u₃.mem, u₂.mem, u₁.mem, hm, iv0, c128]
    rw [u₆.mem, u₅.gpr, u₅.mem, iv4, r₄, c132, m₄,
      show VG.Proof.Rc2.X86.Stream.Init.cA s₀ + BitVec.ofNat 64 132 = VG.Proof.Rc2.X86.Stream.Init.cA s₀ + BitVec.ofNat 64 128 + BitVec.ofNat 64 4 by
        rw [Offset.add_add],
      ← Word32.write64_pair, ← Word32.read64_pair]
  have cv₆ : Spec.Rc2.blockAt s₆.mem (VG.Proof.Rc2.X86.Stream.Init.cA s₀ + BitVec.ofNat 64 128) = Spec.Rc2.blockAt s₀.mem (VG.Proof.Rc2.X86.Stream.Init.ivA s₀) := by
    rw [m₆, blockAt_copy]
  -- Our caller's registers.
  refine VG.Proof.Rc2.X86.Stream.Init.wp_arg hp c₆ (i := 6) (by decide) fun s₇ u₇ => ?_
  have c₇ := c₆.upd u₇ (by decide) (by decide) (by decide)
  have g₇ (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ecx) (h₃ : r ≠ .edx) : s₇.gpr r = s.gpr r := by
    rw [u₇.other _ h₁, u₆.gpr, u₅.other _ h₃, u₄.gpr, u₃.other _ h₃, u₂.other _ h₂, u₁.other _ h₁]
  refine wp_stm (o := 512) (B := VG.Proof.Rc2.X86.Stream.Init.scr s₀) u₇.gpr (by rw [u₇.wr, c₆.wr]; exact scIn 512 (by decide)) fun s₈ u₈ => ?_
  have c₈ := c₇.store u₈ (r := VG.Proof.Rc2.X86.Stream.Init.scR s₀) (by simp) (scC 512 (by decide))
  refine wp_stm (o := 516) (B := VG.Proof.Rc2.X86.Stream.Init.scr s₀) (by rw [u₈.gpr]; exact u₇.gpr) (by rw [u₈.wr, c₇.wr]; exact scIn 516 (by decide))
    fun s₉ u₉ => ?_
  have c₉ := c₈.store u₉ (r := VG.Proof.Rc2.X86.Stream.Init.scR s₀) (by simp) (scC 516 (by decide))
  have m₉ : s₉.mem = (s₇.mem.writeW (addr (VG.Proof.Rc2.X86.Stream.Init.scr s₀) 512) (s₀.gpr .ebx)).writeW (addr (VG.Proof.Rc2.X86.Stream.Init.scr s₀) 516)
      (s₀.gpr .esi) := by
    rw [u₉.mem, u₈.mem, u₈.gpr, g₇ _ (by decide) (by decide) (by decide),
      g₇ _ (by decide) (by decide) (by decide), hb, hs]
  have f₉ : Frame [VG.Proof.Rc2.X86.Stream.Init.scR s₀] s₇.mem s₉.mem := by
    rw [m₉]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (scC 512 (by decide))).writeW
      (List.mem_singleton_self _) _ (scC 516 (by decide))
  have cv₉ : Spec.Rc2.blockAt s₉.mem (VG.Proof.Rc2.X86.Stream.Init.cA s₀ + BitVec.ofNat 64 128) = Spec.Rc2.blockAt s₀.mem (VG.Proof.Rc2.X86.Stream.Init.ivA s₀) := by
    rw [Proof.Rc2.blockAt_frame f₉ _ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.c_s.sub_left VG.Proof.Rc2.X86.Stream.Init.cv_sub), u₇.mem]
    exact cv₆
  have w₁ : s₉.mem.readW (addr (VG.Proof.Rc2.X86.Stream.Init.scr s₀) 512) 32 = s₀.gpr .ebx := by
    rw [m₉, Mem.readW_writeW_sep _ (by decide), Mem.readW_writeW_self32]
    rw [hp.scr_addr (d := 512) (by decide), hp.scr_addr (d := 516) (by decide)]
    exact Offset.sep _ (by decide) (by decide) (by decide)
  have w₂ : s₉.mem.readW (addr (VG.Proof.Rc2.X86.Stream.Init.scr s₀) 516) 32 = s₀.gpr .esi := by rw [m₉, Mem.readW_writeW_self32]
  -- The arguments.
  refine wp_mov fun s₁₀ u₁₀ => ?_
  have c₁₀ := c₉.upd u₁₀ (by decide) (by decide) (by decide)
  refine wp_mov fun s₁₁ u₁₁ => ?_
  have c₁₁ := c₁₀.upd u₁₁ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Init.wp_arg hp c₁₁ (i := 2) (by decide) fun s₁₂ u₁₂ => ?_
  have c₁₂ := c₁₁.upd u₁₂ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Init.wp_arg hp c₁₂ (i := 1) (by decide) fun s₁₃ u₁₃ => ?_
  have c₁₃ := c₁₂.upd u₁₃ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Init.wp_arg hp c₁₃ (i := 0) (by decide) fun s₁₄ u₁₄ => WP.block_nil ?_
  have mem : s₁₄.mem = s₉.mem := by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem]
  refine hQ s₁₄ (c₁₃.upd u₁₄ (by decide) (by decide) (by decide)) u₁₄.gpr
    (by rw [u₁₄.other _ (by decide), u₁₃.gpr])
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr])
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide),
      u₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide)]; exact u₂.gpr)
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.gpr, u₉.gpr, u₈.gpr]; exact u₇.gpr)
    (by rw [mem]; exact cv₉) (by rw [mem]; exact w₁) (by rw [mem]; exact w₂)

end VG.Proof.Rc2.X86.Stream.Init

end

/-!
# Streaming RC2-CBC on x86 (32-bit): `init` is correct

The call of the verified key expansion (`keyCall_ok`) and `init_correct`: the
error code for invalid lengths, and otherwise the context.
-/

namespace VG.Proof.Rc2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

abbrev rs5 : List Reg := [.ebx, .esi, .edx, .ecx, .eax]

theorem key_nosp : NoSp Impl.Rc2.X86.expandKey := NoSp.of_all (by lit_decide)

theorem key_stack : stackUse Impl.Rc2.X86.expandKey = 0 := by decide

def callRd (s₀ s : State) : List Region := [VG.Proof.Rc2.X86.Stream.Init.keyR s₀, ⟨VG.X86.argAddr (pushed VG.Proof.Rc2.X86.Stream.Init.rs5 s).callEntry 0, 20⟩]
def callWr (s₀ : State) : List Region := [VG.Proof.Rc2.X86.Stream.Init.schR s₀, ⟨VG.Proof.Rc2.X86.Stream.Init.sA s₀, 512⟩]

theorem setWidth_append (a b : BitVec 32) : BitVec.setWidth 32 (a ++ b) = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]
  have := b.isLt
  omega

/-- What the call of `vg_rc2_expand_key(key, key_len, effective_bits, ctx, scratch)` needs. -/
theorem keyCallPre_ok {s₀ s : State} (hp : VG.Proof.Rc2.X86.Stream.Init.Pre s₀) (hk : 1 ≤ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ≤ 128)
    (he : 1 ≤ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ≤ 1024) (hc : VG.Proof.Rc2.X86.Stream.Init.Common s₀ s)
    (eax : s.gpr .eax = VG.Proof.Rc2.X86.Stream.Init.key s₀) (ecx : s.gpr .ecx = VG.X86.arg s₀ 1) (edx : s.gpr .edx = VG.X86.arg s₀ 2)
    (esi : s.gpr .esi = VG.Proof.Rc2.X86.Stream.Init.ctx s₀) (ebx : s.gpr .ebx = VG.Proof.Rc2.X86.Stream.Init.scr s₀) :
    VG.X86.CallPre keyContract VG.Proof.Rc2.X86.Stream.Init.rs5 (VG.Proof.Rc2.X86.Stream.Init.callRd s₀ s) (VG.Proof.Rc2.X86.Stream.Init.callWr s₀) s := by
  have hlo := hp.sp_lo
  have hEf := hp.sp_fit
  have hesp : s.gpr .esp = VG.Proof.Rc2.X86.Stream.Init.E s₀ := hc.esp
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ VG.Proof.Rc2.X86.Stream.Init.rs5 := by decide
  have a0 : VG.X86.arg (pushed VG.Proof.Rc2.X86.Stream.Init.rs5 s).callEntry 0 = VG.Proof.Rc2.X86.Stream.Init.key s₀ := by rw [callEntry_arg fit hrs (by simp)]; exact eax
  have a1 : VG.X86.arg (pushed VG.Proof.Rc2.X86.Stream.Init.rs5 s).callEntry 1 = VG.X86.arg s₀ 1 := by rw [callEntry_arg fit hrs (by simp)]; exact ecx
  have a2 : VG.X86.arg (pushed VG.Proof.Rc2.X86.Stream.Init.rs5 s).callEntry 2 = VG.X86.arg s₀ 2 := by rw [callEntry_arg fit hrs (by simp)]; exact edx
  have a3 : VG.X86.arg (pushed VG.Proof.Rc2.X86.Stream.Init.rs5 s).callEntry 3 = VG.Proof.Rc2.X86.Stream.Init.ctx s₀ := by rw [callEntry_arg fit hrs (by simp)]; exact esi
  have a4 : VG.X86.arg (pushed VG.Proof.Rc2.X86.Stream.Init.rs5 s).callEntry 4 = VG.Proof.Rc2.X86.Stream.Init.scr s₀ := by rw [callEntry_arg fit hrs (by simp)]; exact ebx
  have eSp : (pushed VG.Proof.Rc2.X86.Stream.Init.rs5 s).callEntry.gpr .esp = VG.Proof.Rc2.X86.Stream.Init.E s₀ - BitVec.ofNat 32 24 := by
    rw [callEntry_esp', hesp]; rfl
  have eA : VG.X86.argAddr (pushed VG.Proof.Rc2.X86.Stream.Init.rs5 s).callEntry 0 = (VG.Proof.Rc2.X86.Stream.Init.E s₀ - BitVec.ofNat 32 20).setWidth 64 := by
    rw [callEntry_argAddr0, hesp]; rfl
  have kA' : Region.Sub ⟨(VG.Proof.Rc2.X86.Stream.Init.E s₀ - BitVec.ofNat 32 20).setWidth 64, 20⟩ (VG.Proof.Rc2.X86.Stream.Init.stkR s₀) := below_sub (by decide) hlo
  have kR : Region.Sub ⟨(VG.Proof.Rc2.X86.Stream.Init.E s₀ - BitVec.ofNat 32 24).setWidth 64, 4⟩ (VG.Proof.Rc2.X86.Stream.Init.stkR s₀) := by
    have := below_inner (sp := VG.Proof.Rc2.X86.Stream.Init.E s₀) (a := 4) (b := 24) (k := 20) (by omega) hlo
    rw [show VG.Proof.Rc2.X86.Stream.Init.E s₀ - BitVec.ofNat 32 24 = VG.Proof.Rc2.X86.Stream.Init.E s₀ - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have bS : Region.Sub ⟨VG.Proof.Rc2.X86.Stream.Init.sA s₀, 512⟩ (VG.Proof.Rc2.X86.Stream.Init.scR s₀) := Region.sub_prefix (by decide)
  have wr : s.wr = [VG.Proof.Rc2.X86.Stream.Init.ctxR s₀, VG.Proof.Rc2.X86.Stream.Init.scR s₀] := hc.wr.trans hp.wr
  have rd : s.rd = [VG.Proof.Rc2.X86.Stream.Init.keyR s₀, VG.Proof.Rc2.X86.Stream.Init.ivR s₀, VG.Proof.Rc2.X86.Stream.Init.argR s₀] := hc.rd.trans hp.rd
  have sing {r r' : Region} (h : r.Disjoint r') : ∀ x ∈ [r'], r.Disjoint x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact h
  refine ⟨?_, ?_, ?_⟩
  · simp only [keyContract, VG.Proof.Rc2.X86.Stream.Init.callRd, VG.Proof.Rc2.X86.Stream.Init.callWr, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, addr32]
    refine ⟨trivial, trivial, hp.k_c.sub_right VG.Proof.Rc2.X86.Stream.Init.sch_sub, hp.k_s.sub_right bS,
      (hp.c_s.sub_left VG.Proof.Rc2.X86.Stream.Init.sch_sub).sub_right bS, (hp.t_c.sub_left kA').sub_right VG.Proof.Rc2.X86.Stream.Init.sch_sub,
      (hp.t_s.sub_left kA').sub_right bS, (hp.t_c.sub_left kR).sub_right VG.Proof.Rc2.X86.Stream.Init.sch_sub,
      (hp.t_s.sub_left kR).sub_right bS, hp.k_fit, by have := hp.c_fit; omega,
      by have := hp.s_fit; omega, by rw [sub_toNat (by omega)]; omega, hk.1, hk.2, he.1, he.2⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [VG.Proof.Rc2.X86.Stream.Init.callRd, VG.Proof.Rc2.X86.Stream.Init.callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨VG.Proof.Rc2.X86.Stream.Init.keyR s₀, by simp [rd], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true (by simp)⟩
    · refine ⟨below (s.gpr .esp) (4 * rs5.length), by simp, 0, ?_, by simp⟩
      rw [BitVec.add_zero, callEntry_argAddr0]
    · exact ⟨VG.Proof.Rc2.X86.Stream.Init.ctxR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨VG.Proof.Rc2.X86.Stream.Init.scR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
  · refine Covers.of_sub fun r hr => ?_
    simp only [VG.Proof.Rc2.X86.Stream.Init.callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.Rc2.X86.Stream.Init.ctxR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨VG.Proof.Rc2.X86.Stream.Init.scR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩

/-- The call of `vg_rc2_expand_key(key, key_len, effective_bits, ctx, scratch)`. -/
theorem keyCall_ok {s₀ s : State} (hp : VG.Proof.Rc2.X86.Stream.Init.Pre s₀) (hk : 1 ≤ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ≤ 128)
    (he : 1 ≤ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ≤ 1024) (hc : VG.Proof.Rc2.X86.Stream.Init.Common s₀ s)
    (eax : s.gpr .eax = VG.Proof.Rc2.X86.Stream.Init.key s₀) (ecx : s.gpr .ecx = VG.X86.arg s₀ 1) (edx : s.gpr .edx = VG.X86.arg s₀ 2)
    (esi : s.gpr .esi = VG.Proof.Rc2.X86.Stream.Init.ctx s₀) (ebx : s.gpr .ebx = VG.Proof.Rc2.X86.Stream.Init.scr s₀) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [VG.Proof.Rc2.X86.Stream.Init.schR s₀, ⟨VG.Proof.Rc2.X86.Stream.Init.sA s₀, 512⟩, VG.Proof.Rc2.X86.Stream.Init.stkR s₀] s.mem s'.mem →
      Spec.Rc2.scheduleAt s'.mem (VG.Proof.Rc2.X86.Stream.Init.cA s₀) =
        Spec.Rc2.expandKey (Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Init.kA s₀) (VG.Proof.Rc2.X86.Stream.Init.kl s₀)) (VG.Proof.Rc2.X86.Stream.Init.eb s₀) → Q s') :
    WP isa keyCall s Q := by
  have hlo := hp.sp_lo
  have hEf := hp.sp_fit
  have hesp : s.gpr .esp = VG.Proof.Rc2.X86.Stream.Init.E s₀ := hc.esp
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ VG.Proof.Rc2.X86.Stream.Init.rs5 := by decide
  have hesp : s.gpr .esp = VG.Proof.Rc2.X86.Stream.Init.E s₀ := hc.esp
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; have := hp.sp_lo; omega
  have hrs : Reg.esp ∉ VG.Proof.Rc2.X86.Stream.Init.rs5 := by decide
  have a0 : VG.X86.arg (pushed VG.Proof.Rc2.X86.Stream.Init.rs5 s).callEntry 0 = VG.Proof.Rc2.X86.Stream.Init.key s₀ := by rw [callEntry_arg fit hrs (by simp)]; exact eax
  have a1 : VG.X86.arg (pushed VG.Proof.Rc2.X86.Stream.Init.rs5 s).callEntry 1 = VG.X86.arg s₀ 1 := by rw [callEntry_arg fit hrs (by simp)]; exact ecx
  have a2 : VG.X86.arg (pushed VG.Proof.Rc2.X86.Stream.Init.rs5 s).callEntry 2 = VG.X86.arg s₀ 2 := by rw [callEntry_arg fit hrs (by simp)]; exact edx
  have a3 : VG.X86.arg (pushed VG.Proof.Rc2.X86.Stream.Init.rs5 s).callEntry 3 = VG.Proof.Rc2.X86.Stream.Init.ctx s₀ := by rw [callEntry_arg fit hrs (by simp)]; exact esi
  have sing {r r' : Region} (h : r.Disjoint r') : ∀ x ∈ [r'], r.Disjoint x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact h
  refine WP.callWith (k := keyContract) key_body_correct VG.Proof.Rc2.X86.Stream.Init.key_nosp (by simp) hrs
    (by rw [VG.Proof.Rc2.X86.Stream.Init.key_stack, hesp]; simp only [List.length_cons, List.length_nil]; have := hp.sp_lo; omega)
    (VG.Proof.Rc2.X86.Stream.Init.keyCallPre_ok hp hk he hc eax ecx edx esi ebx) fun s' rd' wr' cs f ⟨s₂, m₂, post⟩ => ?_
  · have ce := callEntry_frame fit hrs
    have kE : Region.Sub (below (s.gpr .esp) (4 * rs5.length + 4)) (VG.Proof.Rc2.X86.Stream.Init.stkR s₀) := by
      rw [hesp]; exact fun _ h => h
    simp only [keyContract, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, m₂, addr32] at post
    rw [Proof.Rc2.bytesAt_frame ce _ _ (by omega) (sing ((hp.t_k.sub_left kE).symm)),
      Proof.Rc2.bytesAt_frame hc.frame _ _ (by omega) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hp.k_c.sub_right VG.Proof.Rc2.X86.Stream.Init.cv_sub
        · exact hp.k_s)] at post
    refine hQ s' rd' wr' cs (f.sub fun r hr => ?_) post
    simp only [VG.Proof.Rc2.X86.Stream.Init.callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.Rc2.X86.Stream.Init.schR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨VG.Proof.Rc2.X86.Stream.Init.sA s₀, 512⟩, by simp, fun _ h => h⟩
    · refine ⟨VG.Proof.Rc2.X86.Stream.Init.stkR s₀, by simp, ?_⟩
      rw [VG.Proof.Rc2.X86.Stream.Init.key_stack, hesp]; exact fun _ h => h

theorem code_err {s₀ : State} (h : VG.Proof.Rc2.X86.Stream.Init.code s₀ ≠ 0) :
    VG.Proof.Rc2.X86.Stream.Init.code s₀ = (if ¬(1 ≤ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ≤ 128) then 1 else if ¬(1 ≤ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ≤ 1024) then 2 else 3) ∧
      ¬((1 ≤ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ≤ 128) ∧ (1 ≤ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ≤ 1024) ∧ VG.Proof.Rc2.X86.Stream.Init.il s₀ = 8) := by
  unfold VG.Proof.Rc2.X86.Stream.Init.code at h ⊢
  by_cases h₁ : 1 ≤ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ≤ 128 <;> by_cases h₂ : 1 ≤ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ≤ 1024 <;>
    by_cases h₃ : VG.Proof.Rc2.X86.Stream.Init.il s₀ = 8 <;> simp [h₁, h₂, h₃] at h ⊢

theorem code_ok {s₀ : State} (h : VG.Proof.Rc2.X86.Stream.Init.code s₀ = 0) :
    (1 ≤ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ≤ 128) ∧ (1 ≤ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ≤ 1024) ∧ VG.Proof.Rc2.X86.Stream.Init.il s₀ = 8 := by
  unfold VG.Proof.Rc2.X86.Stream.Init.code at h
  by_cases h₁ : 1 ≤ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.kl s₀ ≤ 128 <;> by_cases h₂ : 1 ≤ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ∧ VG.Proof.Rc2.X86.Stream.Init.eb s₀ ≤ 1024 <;>
    by_cases h₃ : VG.Proof.Rc2.X86.Stream.Init.il s₀ = 8 <;> simp [h₁, h₂, h₃] at h ⊢ <;> omega

theorem code_lt (s₀ : State) : VG.Proof.Rc2.X86.Stream.Init.code s₀ < 4 := by
  unfold VG.Proof.Rc2.X86.Stream.Init.code; split <;> [skip; split <;> [skip; split]] <;> decide

theorem init_correct (s₀ : State) (hs : initContract.pre s₀) :
    WP isa init s₀ (fun s' => abiPreserved s₀ s' ∧ initContract.post s₀ s') := by
  have hp := VG.Proof.Rc2.X86.Stream.Init.pre_of hs
  rw [init]
  refine WP.seq (VG.Proof.Rc2.X86.Stream.Init.checks_ok hp fun s c m a b e => ?_)
  refine WP.seq (wp_test fun s₁ f₁ hz => WP.block_nil ?_)
  have hz' : s₁.zf = some (decide (VG.Proof.Rc2.X86.Stream.Init.code s₀ = 0)) := by
    rw [hz, a, BitVec.and_self, ofNat_beq_zero (by have := VG.Proof.Rc2.X86.Stream.Init.code_lt s₀; omega)]
  have c₁ := c.fupd f₁
  refine WP.ite (!decide (VG.Proof.Rc2.X86.Stream.Init.code s₀ = 0)) (by show s₁.zf.map (!·) = _; rw [hz']; rfl)
    (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · -- Invalid lengths.
    have h0 : VG.Proof.Rc2.X86.Stream.Init.code s₀ ≠ 0 := of_decide_eq_false (by revert hb; cases decide (VG.Proof.Rc2.X86.Stream.Init.code s₀ = 0) <;> simp)
    obtain ⟨hcode, hbad⟩ := VG.Proof.Rc2.X86.Stream.Init.code_err h0
    refine ⟨⟨?_, by rw [f₁.mem, m]⟩, ?_⟩
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rw [f₁.gpr]
      exacts [b, e, c.edi, c.ebp, c.esp]
    · refine init_post_error (m := s₀.mem) (m' := s₁.mem) (key := VG.Proof.Rc2.X86.Stream.Init.kA s₀) (iv := VG.Proof.Rc2.X86.Stream.Init.ivA s₀) (ctx := VG.Proof.Rc2.X86.Stream.Init.cA s₀)
        (keyLen := VG.Proof.Rc2.X86.Stream.Init.kl s₀) (effectiveBits := VG.Proof.Rc2.X86.Stream.Init.eb s₀) (ivLen := VG.Proof.Rc2.X86.Stream.Init.il s₀) ?_ hbad
      rw [VG.Proof.Rc2.X86.Stream.Init.setWidth_append, f₁.gpr, a, toNat_ofNat_lt (by have := VG.Proof.Rc2.X86.Stream.Init.code_lt s₀; omega)]
      exact hcode
  · have h0 : VG.Proof.Rc2.X86.Stream.Init.code s₀ = 0 := of_decide_eq_true (by revert hb; cases decide (VG.Proof.Rc2.X86.Stream.Init.code s₀ = 0) <;> simp)
    obtain ⟨hk, he, hi⟩ := VG.Proof.Rc2.X86.Stream.Init.code_ok h0
    rw [initBody]
    refine WP.seq (VG.Proof.Rc2.X86.Stream.Init.initArgs_ok hp hi c₁ (by rw [f₁.mem, m]) (by rw [f₁.gpr]; exact b) (by rw [f₁.gpr]; exact e)
      fun t ct ea ec ed es eb' cv w₁ w₂ => ?_)
    refine WP.seq (VG.Proof.Rc2.X86.Stream.Init.keyCall_ok hp hk he ct ea ec ed es eb' fun s' rd' wr' cs f sch => ?_)
    have bS : Region.Sub ⟨VG.Proof.Rc2.X86.Stream.Init.sA s₀, 512⟩ (VG.Proof.Rc2.X86.Stream.Init.scR s₀) := Region.sub_prefix (by decide)
    have sep3 {r : Region} (h₁ : r.Disjoint (VG.Proof.Rc2.X86.Stream.Init.schR s₀)) (h₂ : r.Disjoint ⟨VG.Proof.Rc2.X86.Stream.Init.sA s₀, 512⟩) (h₃ : r.Disjoint (VG.Proof.Rc2.X86.Stream.Init.stkR s₀)) :
        ∀ x ∈ [VG.Proof.Rc2.X86.Stream.Init.schR s₀, ⟨VG.Proof.Rc2.X86.Stream.Init.sA s₀, 512⟩, VG.Proof.Rc2.X86.Stream.Init.stkR s₀], r.Disjoint x := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro x (rfl | rfl | rfl)
      exacts [h₁, h₂, h₃]
    have word {d : Nat} (hd : 512 ≤ d) (hd' : d + 4 ≤ 576) :
        s'.mem.readW (addr (VG.Proof.Rc2.X86.Stream.Init.scr s₀) d) 32 = t.mem.readW (addr (VG.Proof.Rc2.X86.Stream.Init.scr s₀) d) 32 := by
      refine f.readW (Region.contains_self _ _) (sep3 ?_ ?_ ?_) (by decide)
      · exact (hp.c_s.sub_left VG.Proof.Rc2.X86.Stream.Init.sch_sub).symm.sub_left (hp.scr_sub hd')
      · rw [hp.scr_addr hd']; exact Offset.disjoint_base _ hd (by omega)
      · exact hp.t_s.symm.sub_left (hp.scr_sub hd')
    have scIn (d : Nat) (hd : d + 4 ≤ 576) : InRegions (s'.rd ++ s'.wr) (addr (VG.Proof.Rc2.X86.Stream.Init.scr s₀) d) 4 := by
      rw [wr', ct.wr, hp.wr, hp.scr_addr hd]
      exact ⟨VG.Proof.Rc2.X86.Stream.Init.scR s₀, by simp, Offset.contains_base _ hd (by omega)⟩
    have ebx' : s'.gpr .ebx = VG.Proof.Rc2.X86.Stream.Init.scr s₀ := by rw [cs _ (by simp [calleeSaved])]; exact eb'
    simp only [restore, List.cons_append, List.nil_append]
    refine wp_ldm (o := 516) ebx' (scIn 516 (by decide)) fun s₂ u₂ => ?_
    refine wp_ldm (o := 512) (B := VG.Proof.Rc2.X86.Stream.Init.scr s₀) (by rw [u₂.other _ (by decide)]; exact ebx')
      (by rw [u₂.rd, u₂.wr]; exact scIn 512 (by decide)) fun s₃ u₃ => ?_
    refine wp_movi fun s₄ u₄ => WP.block_nil ?_
    have mem : s₄.mem = s'.mem := by rw [u₄.mem, u₃.mem, u₂.mem]
    have g (r : Reg) (h₁ : r ≠ .eax) (h₂ : r ≠ .ebx) (h₃ : r ≠ .esi) (hr : r ∈ calleeSaved) :
        s₄.gpr r = t.gpr r := by
      rw [u₄.other _ h₁, u₃.other _ h₂, u₂.other _ h₃]
      exact cs r hr
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, word (by decide) (by decide)]; exact w₁
      · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, word (by decide) (by decide)]; exact w₂
      · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact ct.edi
      · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact ct.ebp
      · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact ct.esp
    · have retStk : (VG.Proof.Rc2.X86.Stream.Init.retR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Init.stkR s₀) := by
        show Region.Disjoint ⟨(VG.Proof.Rc2.X86.Stream.Init.E s₀).setWidth 64, 4⟩ ⟨(VG.Proof.Rc2.X86.Stream.Init.E s₀ - BitVec.ofNat 32 24).setWidth 64, 24⟩
        rw [Taint.sub_setWidth hp.sp_lo]; exact Offset.base_disjoint_below _ (by decide)
      rw [mem, f.readW (Region.contains_self _ _) (sep3 (hp.r_c.sub_right VG.Proof.Rc2.X86.Stream.Init.sch_sub) (hp.r_s.sub_right bS) retStk)
        (by decide)]
      refine ct.frame.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.r_c.sub_right VG.Proof.Rc2.X86.Stream.Init.cv_sub
      · exact hp.r_s
    · refine init_post (m := s₀.mem) (m' := s₄.mem) (key := VG.Proof.Rc2.X86.Stream.Init.kA s₀) (iv := VG.Proof.Rc2.X86.Stream.Init.ivA s₀) (ctx := VG.Proof.Rc2.X86.Stream.Init.cA s₀)
        (keyLen := VG.Proof.Rc2.X86.Stream.Init.kl s₀) (effectiveBits := VG.Proof.Rc2.X86.Stream.Init.eb s₀) (ivLen := VG.Proof.Rc2.X86.Stream.Init.il s₀) hk he hi ?_ ?_ ?_
      · rw [VG.Proof.Rc2.X86.Stream.Init.setWidth_append, u₄.gpr]; rfl
      · rw [mem]; exact sch
      · show Spec.Rc2.blockAt s₄.mem (VG.Proof.Rc2.X86.Stream.Init.cA s₀ + BitVec.ofNat 64 128) = _
        rw [mem, Proof.Rc2.blockAt_frame f _ (sep3 sch_cv.symm ((hp.c_s.sub_left VG.Proof.Rc2.X86.Stream.Init.cv_sub).sub_right bS)
          (hp.t_c.sub_right VG.Proof.Rc2.X86.Stream.Init.cv_sub).symm)]
        exact cv

end VG.Proof.Rc2.X86.Stream.Init

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Stream.UpdateLong`. -/
section

section

section

/-!
# Streaming RC2-CBC on x86 (32-bit): the update functions' precondition

Names for the arguments and regions of an update (`Pre`), and what holds from
the saving of our caller's registers on (`Common`): the arguments are never
written, so they can be read at any point (`wp_arg`).
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp

theorem ofNat_toNat (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by simp

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev ctx : BitVec 32 := VG.X86.arg s₀ 0
abbrev p : Nat := (VG.X86.arg s₀ 1).toNat
abbrev dp : BitVec 32 := VG.X86.arg s₀ 2
abbrev len : Nat := (VG.X86.arg s₀ 3).toNat
abbrev op : BitVec 32 := VG.X86.arg s₀ 4
abbrev O : Nat := (VG.X86.arg s₀ 5).toNat
abbrev scr : BitVec 32 := VG.X86.arg s₀ 6
abbrev cA : Addr := (VG.Proof.Rc2.X86.Stream.Update.ctx s₀).setWidth 64
abbrev dA : Addr := (VG.Proof.Rc2.X86.Stream.Update.dp s₀).setWidth 64
abbrev oA : Addr := (VG.Proof.Rc2.X86.Stream.Update.op s₀).setWidth 64
abbrev sA : Addr := (VG.Proof.Rc2.X86.Stream.Update.scr s₀).setWidth 64
abbrev ctxR : Region := ⟨VG.Proof.Rc2.X86.Stream.Update.cA s₀, 144⟩
abbrev dR : Region := ⟨VG.Proof.Rc2.X86.Stream.Update.dA s₀, VG.Proof.Rc2.X86.Stream.Update.len s₀⟩
abbrev oR : Region := ⟨VG.Proof.Rc2.X86.Stream.Update.oA s₀, VG.Proof.Rc2.X86.Stream.Update.O s₀⟩
abbrev scR : Region := ⟨VG.Proof.Rc2.X86.Stream.Update.sA s₀, 576⟩
abbrev argR : Region := ⟨VG.X86.argAddr s₀ 0, 28⟩
abbrev retR : Region := ⟨(VG.Proof.Rc2.X86.Stream.Update.E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (VG.Proof.Rc2.X86.Stream.Update.E s₀) 40
/-- The pending block. -/
abbrev pendR : Region := ⟨VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136, 8⟩
/-- The schedule and the chaining value. -/
abbrev schR : Region := ⟨VG.Proof.Rc2.X86.Stream.Update.cA s₀, 128⟩
abbrev ivR : Region := ⟨VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 128, 8⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Rc2.X86.Stream.Update.dR s₀, VG.Proof.Rc2.X86.Stream.Update.argR s₀]
  wr : s₀.wr = [VG.Proof.Rc2.X86.Stream.Update.ctxR s₀, VG.Proof.Rc2.X86.Stream.Update.oR s₀, VG.Proof.Rc2.X86.Stream.Update.scR s₀]
  c_d : (VG.Proof.Rc2.X86.Stream.Update.ctxR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.dR s₀)
  c_o : (VG.Proof.Rc2.X86.Stream.Update.ctxR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.oR s₀)
  c_s : (VG.Proof.Rc2.X86.Stream.Update.ctxR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.scR s₀)
  d_o : (VG.Proof.Rc2.X86.Stream.Update.dR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.oR s₀)
  d_s : (VG.Proof.Rc2.X86.Stream.Update.dR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.scR s₀)
  o_s : (VG.Proof.Rc2.X86.Stream.Update.oR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.scR s₀)
  a_c : (VG.Proof.Rc2.X86.Stream.Update.argR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.ctxR s₀)
  a_o : (VG.Proof.Rc2.X86.Stream.Update.argR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.oR s₀)
  a_s : (VG.Proof.Rc2.X86.Stream.Update.argR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.scR s₀)
  r_c : (VG.Proof.Rc2.X86.Stream.Update.retR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.ctxR s₀)
  r_o : (VG.Proof.Rc2.X86.Stream.Update.retR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.oR s₀)
  r_s : (VG.Proof.Rc2.X86.Stream.Update.retR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.scR s₀)
  k_c : (VG.Proof.Rc2.X86.Stream.Update.stkR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.ctxR s₀)
  k_d : (VG.Proof.Rc2.X86.Stream.Update.stkR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.dR s₀)
  k_o : (VG.Proof.Rc2.X86.Stream.Update.stkR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.oR s₀)
  k_s : (VG.Proof.Rc2.X86.Stream.Update.stkR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.scR s₀)
  c_fit : (VG.Proof.Rc2.X86.Stream.Update.ctx s₀).toNat + 144 ≤ 2 ^ 32
  d_fit : (VG.Proof.Rc2.X86.Stream.Update.dp s₀).toNat + VG.Proof.Rc2.X86.Stream.Update.len s₀ ≤ 2 ^ 32
  o_fit : (VG.Proof.Rc2.X86.Stream.Update.op s₀).toNat + VG.Proof.Rc2.X86.Stream.Update.O s₀ ≤ 2 ^ 32
  s_fit : (VG.Proof.Rc2.X86.Stream.Update.scr s₀).toNat + 576 ≤ 2 ^ 32
  sp_lo : 40 ≤ (VG.Proof.Rc2.X86.Stream.Update.E s₀).toNat
  sp_fit : (VG.Proof.Rc2.X86.Stream.Update.E s₀).toNat + 32 ≤ 2 ^ 32
  p_lt : VG.Proof.Rc2.X86.Stream.Update.p s₀ < 8
  O_eq : VG.Proof.Rc2.X86.Stream.Update.O s₀ = (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) / 8 * 8

theorem pre_of {d : Spec.Rc2.Direction} {s₀ : State} (h : (VG.Proof.Rc2.X86.Stream.updateContract d).pre s₀) : VG.Proof.Rc2.X86.Stream.Update.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24, h25, h26⟩

namespace Pre
variable {s₀ : State} (hp : VG.Proof.Rc2.X86.Stream.Update.Pre s₀)
include hp

theorem argAddr_eq (i : Nat) (hi : i < 7) :
    addr (VG.Proof.Rc2.X86.Stream.Update.E s₀) (4 + 4 * i) = (VG.Proof.Rc2.X86.Stream.Update.E s₀).setWidth 64 + BitVec.ofNat 64 (4 + 4 * i) := by
  have := hp.sp_fit; exact addr_eq (by omega)

theorem arg_sub {i : Nat} (hi : i < 7) : Region.Sub ⟨addr (VG.Proof.Rc2.X86.Stream.Update.E s₀) (4 + 4 * i), 4⟩ (VG.Proof.Rc2.X86.Stream.Update.argR s₀) := by
  show Region.Sub _ ⟨addr (VG.Proof.Rc2.X86.Stream.Update.E s₀) (4 + 4 * 0), 28⟩
  rw [hp.argAddr_eq i hi, hp.argAddr_eq 0 (by decide)]
  exact Offset.sub _ (by omega) (by omega)

omit hp in
theorem pend_sub : Region.Sub (VG.Proof.Rc2.X86.Stream.Update.pendR s₀) (VG.Proof.Rc2.X86.Stream.Update.ctxR s₀) := Offset.sub_base _ (by decide)
omit hp in
theorem sch_sub : Region.Sub (VG.Proof.Rc2.X86.Stream.Update.schR s₀) (VG.Proof.Rc2.X86.Stream.Update.ctxR s₀) := Region.sub_prefix (by decide)
omit hp in
theorem iv_sub : Region.Sub (VG.Proof.Rc2.X86.Stream.Update.ivR s₀) (VG.Proof.Rc2.X86.Stream.Update.ctxR s₀) := Offset.sub_base _ (by decide)

omit hp in
theorem sch_pend : (VG.Proof.Rc2.X86.Stream.Update.schR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.pendR s₀) := Offset.base_disjoint _ (by decide) (by decide)
omit hp in
theorem iv_pend : (VG.Proof.Rc2.X86.Stream.Update.ivR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.pendR s₀) := Offset.disjoint _ (by decide) (by decide) (by decide)
omit hp in
theorem sch_iv : (VG.Proof.Rc2.X86.Stream.Update.schR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.ivR s₀) := Offset.base_disjoint _ (by decide) (by decide)

/-- A word of the scratch space. -/
theorem scr_addr {d : Nat} (hd : d + 4 ≤ 576) : addr (VG.Proof.Rc2.X86.Stream.Update.scr s₀) d = VG.Proof.Rc2.X86.Stream.Update.sA s₀ + BitVec.ofNat 64 d := by
  have := hp.s_fit; exact addr_eq (by omega)

theorem scr_sub {d : Nat} (hd : d + 4 ≤ 576) : Region.Sub ⟨addr (VG.Proof.Rc2.X86.Stream.Update.scr s₀) d, 4⟩ (VG.Proof.Rc2.X86.Stream.Update.scR s₀) := by
  rw [hp.scr_addr hd]; exact Offset.sub_base _ hd

theorem sin {s : State} (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 576) :
    InRegions s.wr (addr (VG.Proof.Rc2.X86.Stream.Update.scr s₀) d) 4 :=
  ⟨VG.Proof.Rc2.X86.Stream.Update.scR s₀, by simp [hwr, hp.wr], by rw [hp.scr_addr hd]; exact Offset.contains_base _ hd (by omega)⟩

theorem rin {s : State} (hrd : s.rd = s₀.rd) {i : Nat} (hi : i < 7) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Rc2.X86.Stream.Update.E s₀) (4 + 4 * i)) 4 := by
  refine ⟨VG.Proof.Rc2.X86.Stream.Update.argR s₀, by simp [hrd, hp.rd], ?_⟩
  show (⟨addr (VG.Proof.Rc2.X86.Stream.Update.E s₀) (4 + 4 * 0), 28⟩ : Region).Contains _ _
  rw [hp.argAddr_eq i hi, hp.argAddr_eq 0 (by decide)]
  exact Offset.contains _ (by omega) (by omega) (by have := hp.sp_fit; omega)

/-- The regions written are disjoint from the arguments, the saved words, the
schedule and the chaining value. -/
theorem sep_pend : ∀ r ∈ [VG.Proof.Rc2.X86.Stream.Update.argR s₀, VG.Proof.Rc2.X86.Stream.Update.scR s₀, VG.Proof.Rc2.X86.Stream.Update.schR s₀, VG.Proof.Rc2.X86.Stream.Update.ivR s₀, VG.Proof.Rc2.X86.Stream.Update.dR s₀, VG.Proof.Rc2.X86.Stream.Update.oR s₀, VG.Proof.Rc2.X86.Stream.Update.retR s₀, VG.Proof.Rc2.X86.Stream.Update.stkR s₀],
    r.Disjoint (VG.Proof.Rc2.X86.Stream.Update.pendR s₀) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact hp.a_c.sub_right Pre.pend_sub
  · exact (hp.c_s.sub_left Pre.pend_sub).symm
  · exact Pre.sch_pend
  · exact Pre.iv_pend
  · exact (hp.c_d.sub_left Pre.pend_sub).symm
  · exact (hp.c_o.sub_left Pre.pend_sub).symm
  · exact hp.r_c.sub_right Pre.pend_sub
  · exact hp.k_c.sub_right Pre.pend_sub

end Pre

/-! ## From the saving of our caller's registers on -/

structure Common (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = VG.Proof.Rc2.X86.Stream.Update.E s₀
  edi : s.gpr .edi = s₀.gpr .edi
  ebp : s.gpr .ebp = s₀.gpr .ebp
  frame : Frame [VG.Proof.Rc2.X86.Stream.Update.pendR s₀, VG.Proof.Rc2.X86.Stream.Update.oR s₀, VG.Proof.Rc2.X86.Stream.Update.scR s₀] s₀.mem s.mem
  ebx : s.mem.readW (addr (VG.Proof.Rc2.X86.Stream.Update.scr s₀) 512) 32 = s₀.gpr .ebx
  esi : s.mem.readW (addr (VG.Proof.Rc2.X86.Stream.Update.scr s₀) 516) 32 = s₀.gpr .esi

theorem Common.arg {s₀ s : State} (hp : VG.Proof.Rc2.X86.Stream.Update.Pre s₀) (h : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s) {i : Nat} (hi : i < 7) :
    s.mem.readW (addr (VG.Proof.Rc2.X86.Stream.Update.E s₀) (4 + 4 * i)) 32 = VG.X86.arg s₀ i := by
  have hs := hp.arg_sub hi
  refine (h.frame.readW (Region.contains_self _ _) ?_ (by decide)).trans rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ((hp.sep_pend _ (by simp)).sub_left hs)
  · exact hp.a_o.sub_left hs
  · exact hp.a_s.sub_left hs

/-- `mov d, [esp + 4 + 4i]`: argument `i`. -/
theorem wp_arg {s₀ s : State} (hp : VG.Proof.Rc2.X86.Stream.Update.Pre s₀) (h : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s) {i : Nat} (hi : i < 7) {d : Reg}
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (VG.X86.arg s₀ i) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem (Impl.Rc2.X86.Stream.argOp i)) :: is)) s Q :=
  wp_ldm (b := .esp) (o := 4 + 4 * i) h.esp (hp.rin h.rd hi) fun s' u => k s' (h.arg hp hi ▸ u)

/-- `Common` after writing within the pending block or `out`. -/
theorem Common.write {s₀ s s' : State} (hp : VG.Proof.Rc2.X86.Stream.Update.Pre s₀) (h : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s) {r : Region}
    (hr : Region.Sub r (VG.Proof.Rc2.X86.Stream.Update.pendR s₀) ∨ Region.Sub r (VG.Proof.Rc2.X86.Stream.Update.oR s₀)) (f : Frame [r] s.mem s'.mem)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hesp : s'.gpr .esp = s.gpr .esp)
    (hedi : s'.gpr .edi = s.gpr .edi) (hebp : s'.gpr .ebp = s.gpr .ebp) : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s' := by
  have sd : ∀ {e : Nat}, e + 4 ≤ 576 → r.Disjoint ⟨addr (VG.Proof.Rc2.X86.Stream.Update.scr s₀) e, 4⟩ := fun he => by
    rcases hr with hr | hr
    · exact ((hp.c_s.sub_left Pre.pend_sub).sub_left hr).sub_right (hp.scr_sub he)
    · exact (hp.o_s.sub_left hr).sub_right (hp.scr_sub he)
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hesp.trans h.esp, hedi.trans h.edi, hebp.trans h.ebp,
    h.frame.trans (f.sub ?_), ?_, ?_⟩
  · intro r' hr'
    simp only [List.mem_singleton] at hr'; subst hr'
    rcases hr with hr | hr
    · exact ⟨_, by simp, hr⟩
    · exact ⟨_, by simp, hr⟩
  · rw [f.readW (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact (sd (by decide)).symm) (by decide)]
    exact h.ebx
  · rw [f.readW (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'; exact (sd (by decide)).symm) (by decide)]
    exact h.esi

end VG.Proof.Rc2.X86.Stream.Update

end

/-!
# Streaming RC2-CBC on x86 (32-bit): the copies of the update functions

Saving our caller's registers (`entry_ok`), and the copies: with no complete
block, the data after the pending bytes (`short_ok`); otherwise the pending
bytes and the first `out_len - pending_len` bytes of data to `out` and the
rest to the pending block (`long_ok`).
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream
open VG.WriteBytes (writeBytes writeBytes_frame)

theorem Common.upd {s₀ s s' : State} (h : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s) {d : Reg} {v : BitVec 32} (u : Upd s s' d v)
    (h₁ : d ≠ .esp) (h₂ : d ≠ .edi) (h₃ : d ≠ .ebp) : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, (u.other _ (Ne.symm h₁)).trans h.esp,
    (u.other _ (Ne.symm h₂)).trans h.edi, (u.other _ (Ne.symm h₃)).trans h.ebp,
    by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.ebx, by rw [u.mem]; exact h.esi⟩

theorem Common.fupd {s₀ s s' : State} (h : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s) (u : Fupd s s') : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s' :=
  ⟨u.rd.trans h.rd, u.wr.trans h.wr, by rw [u.gpr]; exact h.esp, by rw [u.gpr]; exact h.edi,
    by rw [u.gpr]; exact h.ebp, by rw [u.mem]; exact h.frame, by rw [u.mem]; exact h.ebx,
    by rw [u.mem]; exact h.esi⟩

theorem frame_writeBytes (m : Mem) (q : Addr) (xs : List Byte) : Frame [⟨q, xs.length⟩] m (writeBytes m q xs) :=
  writeBytes_frame _ _ _ (Region.contains_self _ _)

/-- A copy leaves `Common`, if it writes within the pending block or `out`. -/
theorem Common.copy {s₀ s s' : State} (hp : VG.Proof.Rc2.X86.Stream.Update.Pre s₀) (h : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s) {S D : BitVec 32} {sd dd n : Nat}
    (c : VG.Proof.Rc2.X86.Stream.CopyPost s S D sd dd n s')
    (hr : Region.Sub ⟨addr D dd, n⟩ (VG.Proof.Rc2.X86.Stream.Update.pendR s₀) ∨ Region.Sub ⟨addr D dd, n⟩ (VG.Proof.Rc2.X86.Stream.Update.oR s₀)) : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s' := by
  refine h.write hp hr ?_ c.rd c.wr (c.other _ (by decide) (by decide) (by decide) (by decide))
    (c.other _ (by decide) (by decide) (by decide) (by decide))
    (c.other _ (by decide) (by decide) (by decide) (by decide))
  have := VG.Proof.Rc2.X86.Stream.Update.frame_writeBytes s.mem (addr D dd) (Spec.Rc2.bytesAt s.mem (addr S sd) n)
  rwa [VG.Proof.Rc2.X86.Stream.bytesAt_len, ← c.mem] at this

theorem copy_bytes {s s' : State} {S D : BitVec 32} {sd dd n : Nat} (c : VG.Proof.Rc2.X86.Stream.CopyPost s S D sd dd n s')
    (hn : n < 2 ^ 64) :
    Spec.Rc2.bytesAt s'.mem (addr D dd) n = Spec.Rc2.bytesAt s.mem (addr S sd) n := by
  have h := VG.Proof.Rc2.X86.Stream.bytesAt_writeBytes_self s.mem (addr D dd) (Spec.Rc2.bytesAt s.mem (addr S sd) n)
    (by rw [VG.Proof.Rc2.X86.Stream.bytesAt_len]; exact hn)
  rwa [VG.Proof.Rc2.X86.Stream.bytesAt_len, ← c.mem] at h

theorem copy_frame {s s' : State} {S D : BitVec 32} {sd dd n : Nat} (c : VG.Proof.Rc2.X86.Stream.CopyPost s S D sd dd n s') :
    Frame [⟨addr D dd, n⟩] s.mem s'.mem := by
  have := VG.Proof.Rc2.X86.Stream.Update.frame_writeBytes s.mem (addr D dd) (Spec.Rc2.bytesAt s.mem (addr S sd) n)
  rwa [VG.Proof.Rc2.X86.Stream.bytesAt_len, ← c.mem] at this

/-! ## Saving our caller's registers -/

theorem entry_ok {s₀ : State} (hp : VG.Proof.Rc2.X86.Stream.Update.Pre s₀) {Q : State → Prop}
    (hQ : ∀ s, VG.Proof.Rc2.X86.Stream.Update.Common s₀ s → Frame [VG.Proof.Rc2.X86.Stream.Update.scR s₀] s₀.mem s.mem → s.zf = some (decide (VG.Proof.Rc2.X86.Stream.Update.O s₀ = 0)) → Q s) :
    WP isa (.block entry) s₀ Q := by
  simp only [entry, save, List.cons_append, List.nil_append]
  have sc (d : Nat) (hd : d + 4 ≤ 576) : (VG.Proof.Rc2.X86.Stream.Update.scR s₀).Contains (addr (VG.Proof.Rc2.X86.Stream.Update.scr s₀) d) (32 / 8) := by
    rw [hp.scr_addr hd]; exact Offset.contains_base _ hd (by omega)
  refine wp_ldm (b := .esp) (o := 4 + 4 * 6) rfl (hp.rin rfl (by decide)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = VG.Proof.Rc2.X86.Stream.Update.scr s₀ := u₁.gpr
  refine wp_stm e₁ (hp.sin (u₁.wr) (d := 512) (by decide)) fun s₂ u₂ => ?_
  refine wp_stm (by rw [u₂.gpr]; exact e₁) (hp.sin (u₂.wr.trans u₁.wr) (d := 516) (by decide))
    fun s₃ u₃ => ?_
  have m₃ : s₃.mem = (s₀.mem.writeW (addr (VG.Proof.Rc2.X86.Stream.Update.scr s₀) 512) (s₀.gpr .ebx)).writeW (addr (VG.Proof.Rc2.X86.Stream.Update.scr s₀) 516)
      (s₀.gpr .esi) := by
    rw [u₃.mem, u₂.mem, u₂.gpr, u₁.mem, u₁.other _ (by decide), u₁.other _ (by decide)]
  have f₃ : Frame [VG.Proof.Rc2.X86.Stream.Update.scR s₀] s₀.mem s₃.mem := by
    rw [m₃]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sc 512 (by decide))).writeW
      (List.mem_singleton_self _) _ (sc 516 (by decide))
  have g₃ (r : Reg) (hr : r ≠ .eax) : s₃.gpr r = s₀.gpr r := by
    rw [u₃.gpr, u₂.gpr]; exact u₁.other r hr
  have c₃ : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s₃ := by
    refine ⟨by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr], g₃ _ (by decide), g₃ _ (by decide),
      g₃ _ (by decide), f₃.mono (by simp), ?_, ?_⟩
    · rw [m₃, Mem.readW_writeW_sep _ (by decide), Mem.readW_writeW_self32]
      rw [hp.scr_addr (d := 512) (by decide), hp.scr_addr (d := 516) (by decide)]
      exact Offset.sep _ (by decide) (by decide) (by decide)
    · rw [m₃, Mem.readW_writeW_self32]
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp c₃ (i := 5) (by decide) fun s₄ u₄ => wp_test fun s₅ f₅ hz₅ => WP.block_nil ?_
  refine hQ s₅ ((c₃.upd u₄ (by decide) (by decide) (by decide)).fupd f₅) (by rw [f₅.mem, u₄.mem]; exact f₃) ?_
  rw [hz₅, u₄.gpr, BitVec.and_self, ← VG.Proof.Rc2.X86.Stream.Update.ofNat_toNat (VG.X86.arg s₀ 5), ofNat_beq_zero (VG.X86.arg s₀ 5).isLt]

/-! ## No complete block -/

theorem short_ok {s₀ s : State} (hp : VG.Proof.Rc2.X86.Stream.Update.Pre s₀) (hO : VG.Proof.Rc2.X86.Stream.Update.O s₀ = 0) (hc : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s)
    (hf : Frame [VG.Proof.Rc2.X86.Stream.Update.scR s₀] s₀.mem s.mem) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Rc2.X86.Stream.Update.Common s₀ s' →
      Spec.Rc2.bytesAt s'.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136) (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) =
        Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136) (VG.Proof.Rc2.X86.Stream.Update.p s₀) ++
          Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.dA s₀) (VG.Proof.Rc2.X86.Stream.Update.len s₀) → Q s') :
    WP isa short s Q := by
  have hpl : VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀ < 8 := by have := hp.O_eq; omega
  have hcf := hp.c_fit
  have hdf := hp.d_fit
  rw [short]
  refine WP.seq ?_
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp hc (i := 2) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp c₁ (i := 0) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp c₂ (i := 1) (by decide) fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_add fun s₄ u₄ _ => ?_
  have c₄ := c₃.upd u₄ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp c₄ (i := 3) (by decide) fun s₅ u₅ => WP.block_nil ?_
  have c₅ := c₄.upd u₅ (by decide) (by decide) (by decide)
  have esi₅ : s₅.gpr .esi = VG.Proof.Rc2.X86.Stream.Update.dp s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.gpr]
  have edx₅ : s₅.gpr .edx = VG.Proof.Rc2.X86.Stream.Update.ctx s₀ + BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.p s₀) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₃.gpr, u₂.gpr, VG.Proof.Rc2.X86.Stream.Update.ofNat_toNat]
  have ecx₅ : s₅.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.len s₀) := by rw [u₅.gpr, VG.Proof.Rc2.X86.Stream.Update.ofNat_toNat]
  have mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hS : addr (VG.Proof.Rc2.X86.Stream.Update.dp s₀) 0 = VG.Proof.Rc2.X86.Stream.Update.dA s₀ := by
    rw [addr_eq (by have := (VG.Proof.Rc2.X86.Stream.Update.dp s₀).isLt; omega)]; exact BitVec.add_zero _
  have hD : addr (VG.Proof.Rc2.X86.Stream.Update.ctx s₀ + BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.p s₀)) 136 = VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 (VG.Proof.Rc2.X86.Stream.Update.p s₀ + 136) :=
    VG.Proof.Rc2.X86.Stream.addr_add (by omega)
  have dst : Region.Sub ⟨VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 (VG.Proof.Rc2.X86.Stream.Update.p s₀ + 136), VG.Proof.Rc2.X86.Stream.Update.len s₀⟩ (VG.Proof.Rc2.X86.Stream.Update.pendR s₀) :=
    Offset.sub _ (by omega) (by omega)
  refine VG.Proof.Rc2.X86.Stream.copy_ok (sd := 0) (dd := 136) (n := VG.Proof.Rc2.X86.Stream.Update.len s₀) (S := VG.Proof.Rc2.X86.Stream.Update.dp s₀) (D := VG.Proof.Rc2.X86.Stream.Update.ctx s₀ + BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.p s₀))
    (VG.X86.arg s₀ 3).isLt (by omega) (by rw [VG.Proof.Rc2.X86.Stream.toNat_add_ofNat (by omega)]; omega)
    (fun i hi => by
      rw [c₅.rd, c₅.wr, hS]
      exact VG.Proof.Rc2.X86.Stream.inBytes (R := VG.Proof.Rc2.X86.Stream.Update.dR s₀) (by simp [hp.rd]) (fun _ h => h) (by omega) i hi)
    (fun i hi => by
      rw [c₅.wr, hD]
      exact VG.Proof.Rc2.X86.Stream.inBytes (R := VG.Proof.Rc2.X86.Stream.Update.ctxR s₀) (by simp [hp.wr]) (fun a h => Pre.pend_sub a (dst a h)) (by omega) i hi)
    (by rw [hS, hD]; exact hp.c_d.symm.sub_right (fun a h => Pre.pend_sub a (dst a h)))
    esi₅ edx₅ ecx₅ fun s' c => hQ s' (c₅.copy hp c (.inl (by rw [hD]; exact dst))) ?_
  have hw := VG.Proof.Rc2.X86.Stream.bytesAt_writeBytes s.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136) (VG.Proof.Rc2.X86.Stream.Update.p s₀)
    (Spec.Rc2.bytesAt s.mem (VG.Proof.Rc2.X86.Stream.Update.dA s₀) (VG.Proof.Rc2.X86.Stream.Update.len s₀)) (by rw [VG.Proof.Rc2.X86.Stream.bytesAt_len]; omega)
  rw [VG.Proof.Rc2.X86.Stream.bytesAt_len, Offset.add_add, Nat.add_comm 136] at hw
  rw [c.mem, mem₅, hS, hD, hw,
    Proof.Rc2.bytesAt_frame hf _ _ (by omega) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.c_s.sub_left (fun a h => Pre.pend_sub a (Offset.sub _ (by omega) (by omega) a h)))),
    Proof.Rc2.bytesAt_frame hf _ _ (by omega) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.d_s)]

end VG.Proof.Rc2.X86.Stream.Update

end

/-!
# Streaming RC2-CBC on x86 (32-bit): the copies before CBC

With `out_len ≠ 0`: the pending bytes and the first `out_len - pending_len`
bytes of data to `out`, and the rest of the data to the pending block
(`long_ok`).
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

theorem sub_eq' (x y : BitVec 32) (h : y.toNat ≤ x.toNat) : x - y = BitVec.ofNat 32 (x.toNat - y.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem sub_add_eq (x y z : BitVec 32) (h : y.toNat ≤ z.toNat + x.toNat) :
    x - y + z = BitVec.ofNat 32 (z.toNat + x.toNat - y.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt; have := y.isLt; have := z.isLt
  omega

section
variable {s₀ s : State} (hp : VG.Proof.Rc2.X86.Stream.Update.Pre s₀) (hc : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s) {Q : State → Prop}
include hp hc

theorem toOut₁_ok
    (hQ : ∀ t, VG.Proof.Rc2.X86.Stream.Update.Common s₀ t → t.mem = s.mem → t.gpr .esi = VG.Proof.Rc2.X86.Stream.Update.ctx s₀ → t.gpr .edx = VG.Proof.Rc2.X86.Stream.Update.op s₀ →
      t.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.p s₀) → Q t) :
    WP isa (.block toOut₁) s Q := by
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp hc (i := 0) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp c₁ (i := 4) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp c₂ (i := 1) (by decide) fun s₃ u₃ => WP.block_nil ?_
  exact hQ s₃ (c₂.upd u₃ (by decide) (by decide) (by decide)) (by rw [u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
    (by rw [u₃.other _ (by decide), u₂.gpr]) (by rw [u₃.gpr, VG.Proof.Rc2.X86.Stream.Update.ofNat_toNat])

theorem toOut₂_ok (hpO : VG.Proof.Rc2.X86.Stream.Update.p s₀ ≤ VG.Proof.Rc2.X86.Stream.Update.O s₀)
    (hQ : ∀ t, VG.Proof.Rc2.X86.Stream.Update.Common s₀ t → t.mem = s.mem → t.gpr .esi = VG.Proof.Rc2.X86.Stream.Update.dp s₀ → t.gpr .edx = s.gpr .edx →
      t.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀) → Q t) :
    WP isa (.block toOut₂) s Q := by
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp hc (i := 2) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp c₁ (i := 5) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp c₂ (i := 1) (by decide) fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_sub fun s₄ u₄ _ => WP.block_nil ?_
  refine hQ s₄ (c₃.upd u₄ (by decide) (by decide) (by decide)) (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide)]) ?_
  rw [u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₃.gpr]
  exact VG.Proof.Rc2.X86.Stream.Update.sub_eq' _ _ hpO

theorem toPending_ok (hle : VG.Proof.Rc2.X86.Stream.Update.O s₀ ≤ VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀)
    (hQ : ∀ t, VG.Proof.Rc2.X86.Stream.Update.Common s₀ t → t.mem = s.mem → t.gpr .esi = s.gpr .esi → t.gpr .edx = VG.Proof.Rc2.X86.Stream.Update.ctx s₀ →
      t.gpr .ecx = BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀ - VG.Proof.Rc2.X86.Stream.Update.O s₀) → Q t) :
    WP isa (.block toPending) s Q := by
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp hc (i := 0) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp c₁ (i := 3) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp c₂ (i := 5) (by decide) fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_sub fun s₄ u₄ _ => ?_
  have c₄ := c₃.upd u₄ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp c₄ (i := 1) (by decide) fun s₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide) (by decide) (by decide)
  refine wp_add fun s₆ u₆ _ => WP.block_nil ?_
  refine hQ s₆ (c₅.upd u₆ (by decide) (by decide) (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]) ?_
  rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.gpr]
  exact VG.Proof.Rc2.X86.Stream.Update.sub_add_eq _ _ _ hle

end

theorem long_ok {s₀ s : State} (hp : VG.Proof.Rc2.X86.Stream.Update.Pre s₀) (hO : VG.Proof.Rc2.X86.Stream.Update.O s₀ ≠ 0) (hc : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s)
    (hf : Frame [VG.Proof.Rc2.X86.Stream.Update.scR s₀] s₀.mem s.mem) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Rc2.X86.Stream.Update.Common s₀ s' →
      Spec.Rc2.bytesAt s'.mem (VG.Proof.Rc2.X86.Stream.Update.oA s₀) (VG.Proof.Rc2.X86.Stream.Update.O s₀) =
        Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136) (VG.Proof.Rc2.X86.Stream.Update.p s₀) ++
          Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.dA s₀) (VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀) →
      Spec.Rc2.bytesAt s'.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136) ((VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8) =
        Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.dA s₀ + BitVec.ofNat 64 (VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀)) ((VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8) → Q s') :
    WP isa long s Q := by
  have hOe := hp.O_eq
  have hpl := hp.p_lt
  have hpO : VG.Proof.Rc2.X86.Stream.Update.p s₀ ≤ VG.Proof.Rc2.X86.Stream.Update.O s₀ := by omega
  have hOL : VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀ ≤ VG.Proof.Rc2.X86.Stream.Update.len s₀ := by omega
  have hR : VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀ - VG.Proof.Rc2.X86.Stream.Update.O s₀ = (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8 := by omega
  have hRlt : (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8 < 8 := Nat.mod_lt _ (by decide)
  have hcf := hp.c_fit
  have hdf := hp.d_fit
  have hof := hp.o_fit
  have hlen : VG.Proof.Rc2.X86.Stream.Update.len s₀ < 2 ^ 32 := (VG.X86.arg s₀ 3).isLt
  have hOlt : VG.Proof.Rc2.X86.Stream.Update.O s₀ < 2 ^ 32 := (VG.X86.arg s₀ 5).isLt
  have hC : addr (VG.Proof.Rc2.X86.Stream.Update.ctx s₀) 136 = VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136 := addr_eq (by omega)
  have hS : addr (VG.Proof.Rc2.X86.Stream.Update.dp s₀) 0 = VG.Proof.Rc2.X86.Stream.Update.dA s₀ := by
    rw [addr_eq (by have := (VG.Proof.Rc2.X86.Stream.Update.dp s₀).isLt; omega)]; exact BitVec.add_zero _
  have hO0 : addr (VG.Proof.Rc2.X86.Stream.Update.op s₀) 0 = VG.Proof.Rc2.X86.Stream.Update.oA s₀ := by
    rw [addr_eq (by have := (VG.Proof.Rc2.X86.Stream.Update.op s₀).isLt; omega)]; exact BitVec.add_zero _
  have hOp : addr (VG.Proof.Rc2.X86.Stream.Update.op s₀ + BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.p s₀)) 0 = VG.Proof.Rc2.X86.Stream.Update.oA s₀ + BitVec.ofNat 64 (VG.Proof.Rc2.X86.Stream.Update.p s₀) := by
    rw [VG.Proof.Rc2.X86.Stream.addr_add (by omega), Nat.add_zero]
  have hSp (h0 : 0 < (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8) :
      addr (VG.Proof.Rc2.X86.Stream.Update.dp s₀ + BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀)) 0 = VG.Proof.Rc2.X86.Stream.Update.dA s₀ + BitVec.ofNat 64 (VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀) := by
    rw [VG.Proof.Rc2.X86.Stream.addr_add (by omega), Nat.add_zero]
  have inR {a : Addr} {n : Nat} {R : Region} (hR : R ∈ s₀.rd ++ s₀.wr) (hs : Region.Sub ⟨a, n⟩ R)
      (hn : n < 2 ^ 64) {t : State} (hc : VG.Proof.Rc2.X86.Stream.Update.Common s₀ t) :
      ∀ i < n, InRegions (t.rd ++ t.wr) (a + BitVec.ofNat 64 i) 1 := by
    rw [hc.rd, hc.wr]; exact VG.Proof.Rc2.X86.Stream.inBytes hR hs hn
  have outR {a : Addr} {n : Nat} {R : Region} (hR : R ∈ s₀.wr) (hs : Region.Sub ⟨a, n⟩ R)
      (hn : n < 2 ^ 64) {t : State} (hc : VG.Proof.Rc2.X86.Stream.Update.Common s₀ t) : ∀ i < n, InRegions t.wr (a + BitVec.ofNat 64 i) 1 := by
    rw [hc.wr]; exact VG.Proof.Rc2.X86.Stream.inBytes hR hs hn
  have ctxIn : VG.Proof.Rc2.X86.Stream.Update.ctxR s₀ ∈ s₀.wr := by simp [hp.wr]
  have oIn : VG.Proof.Rc2.X86.Stream.Update.oR s₀ ∈ s₀.wr := by simp [hp.wr]
  have ctxIn' : VG.Proof.Rc2.X86.Stream.Update.ctxR s₀ ∈ s₀.rd ++ s₀.wr := List.mem_append_right _ ctxIn
  have dIn : VG.Proof.Rc2.X86.Stream.Update.dR s₀ ∈ s₀.rd ++ s₀.wr := List.mem_append_left _ (by simp [hp.rd])
  have pendSrc : Region.Sub ⟨VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136, VG.Proof.Rc2.X86.Stream.Update.p s₀⟩ (VG.Proof.Rc2.X86.Stream.Update.pendR s₀) := Region.sub_prefix (by omega)
  have pendDst : Region.Sub ⟨VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136, (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8⟩ (VG.Proof.Rc2.X86.Stream.Update.pendR s₀) :=
    Region.sub_prefix (by omega)
  have outA : Region.Sub ⟨VG.Proof.Rc2.X86.Stream.Update.oA s₀, VG.Proof.Rc2.X86.Stream.Update.p s₀⟩ (VG.Proof.Rc2.X86.Stream.Update.oR s₀) := Region.sub_prefix hpO
  have outB : Region.Sub ⟨VG.Proof.Rc2.X86.Stream.Update.oA s₀ + BitVec.ofNat 64 (VG.Proof.Rc2.X86.Stream.Update.p s₀), VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀⟩ (VG.Proof.Rc2.X86.Stream.Update.oR s₀) :=
    Offset.sub_base _ (by omega)
  have datA : Region.Sub ⟨VG.Proof.Rc2.X86.Stream.Update.dA s₀, VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀⟩ (VG.Proof.Rc2.X86.Stream.Update.dR s₀) := Region.sub_prefix hOL
  have datB : Region.Sub ⟨VG.Proof.Rc2.X86.Stream.Update.dA s₀ + BitVec.ofNat 64 (VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀), (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8⟩ (VG.Proof.Rc2.X86.Stream.Update.dR s₀) :=
    Offset.sub_base _ (by omega)
  have pc {r : Region} (h : Region.Sub r (VG.Proof.Rc2.X86.Stream.Update.pendR s₀)) : Region.Sub r (VG.Proof.Rc2.X86.Stream.Update.ctxR s₀) :=
    fun a ha => Pre.pend_sub a (h a ha)
  have sing {r r' : Region} (h : r.Disjoint r') : ∀ x ∈ [r'], r.Disjoint x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact h
  -- The pending bytes to `out`.
  refine WP.seq (VG.Proof.Rc2.X86.Stream.Update.toOut₁_ok hp hc fun s₁ c₁ mem₁ esi₁ edx₁ ecx₁ => ?_)
  refine WP.seq (VG.Proof.Rc2.X86.Stream.copy_ok (sd := 136) (dd := 0) (n := VG.Proof.Rc2.X86.Stream.Update.p s₀) (S := VG.Proof.Rc2.X86.Stream.Update.ctx s₀) (D := VG.Proof.Rc2.X86.Stream.Update.op s₀) (by omega)
    (by omega) (by omega)
    (by rw [hC]; exact inR ctxIn' (pc pendSrc) (by omega) c₁)
    (by rw [hO0]; exact outR oIn outA (by omega) c₁)
    (by rw [hC, hO0]; exact (hp.c_o.sub_left (pc pendSrc)).sub_right outA)
    esi₁ edx₁ ecx₁ fun s₂ k₂ => ?_)
  have c₂ := c₁.copy hp k₂ (.inr (by rw [hO0]; exact outA))
  have f₂ := VG.Proof.Rc2.X86.Stream.Update.copy_frame k₂
  have b₂ := VG.Proof.Rc2.X86.Stream.Update.copy_bytes k₂ (by omega)
  rw [hO0] at f₂ b₂
  rw [hC, mem₁] at b₂
  -- The first `out_len - pending_len` bytes of data after them.
  refine WP.seq (VG.Proof.Rc2.X86.Stream.Update.toOut₂_ok hp c₂ hpO fun s₃ c₃ mem₃ esi₃ edx₃ ecx₃ => ?_)
  rw [k₂.edx] at edx₃
  refine WP.seq (VG.Proof.Rc2.X86.Stream.copy_ok (sd := 0) (dd := 0) (n := VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀) (S := VG.Proof.Rc2.X86.Stream.Update.dp s₀)
    (D := VG.Proof.Rc2.X86.Stream.Update.op s₀ + BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.p s₀)) (by omega) (by omega)
    (by rw [VG.Proof.Rc2.X86.Stream.toNat_add_ofNat (by omega)]; omega)
    (by rw [hS]; exact inR dIn datA (by omega) c₃)
    (by rw [hOp]; exact outR oIn outB (by omega) c₃)
    (by rw [hS, hOp]; exact (hp.d_o.sub_left datA).sub_right outB)
    esi₃ edx₃ ecx₃ fun s₄ k₄ => ?_)
  have c₄ := c₃.copy hp k₄ (.inr (by rw [hOp]; exact outB))
  have f₄ := VG.Proof.Rc2.X86.Stream.Update.copy_frame k₄
  have b₄ := VG.Proof.Rc2.X86.Stream.Update.copy_bytes k₄ (by omega)
  rw [hOp] at f₄ b₄
  rw [hS, mem₃] at b₄
  -- The rest to the pending block.
  refine WP.seq (VG.Proof.Rc2.X86.Stream.Update.toPending_ok hp c₄ (by omega) fun s₅ c₅ mem₅ esi₅ edx₅ ecx₅ => ?_)
  rw [k₄.esi] at esi₅
  rw [hR] at ecx₅
  refine VG.Proof.Rc2.X86.Stream.copy_ok (sd := 0) (dd := 136) (n := (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8)
    (S := VG.Proof.Rc2.X86.Stream.Update.dp s₀ + BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀)) (D := VG.Proof.Rc2.X86.Stream.Update.ctx s₀) (by omega)
    (by
      rcases Nat.eq_zero_or_pos ((VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8) with h0 | h0
      · have := (VG.Proof.Rc2.X86.Stream.Update.dp s₀ + BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀)).isLt; omega
      · rw [VG.Proof.Rc2.X86.Stream.toNat_add_ofNat (by omega)]; omega) (by omega)
    (fun i hi => by rw [hSp (by omega)]; exact inR dIn datB (by omega) c₅ i hi)
    (by rw [hC]; exact outR ctxIn (pc pendDst) (by omega) c₅)
    (by
      rcases Nat.eq_zero_or_pos ((VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8) with h0 | h0
      · intro a h; simp only [Region.Contains, h0] at h; omega
      · rw [hSp h0, hC]; exact (hp.c_d.symm.sub_left datB).sub_right (pc pendDst))
    esi₅ edx₅ ecx₅ fun s₆ k₆ => ?_
  have c₆ := c₅.copy hp k₆ (.inl (by rw [hC]; exact pendDst))
  have f₆ := VG.Proof.Rc2.X86.Stream.Update.copy_frame k₆
  have b₆ := VG.Proof.Rc2.X86.Stream.Update.copy_bytes k₆ (by omega)
  rw [hC] at f₆ b₆
  rw [mem₅] at b₆
  rw [mem₅] at f₆
  rw [mem₃] at f₄
  rw [mem₁] at f₂
  refine hQ s₆ c₆ ?_ ?_
  · -- `out`: the pending bytes, then the data.
    have hsplit : Spec.Rc2.bytesAt s₆.mem (VG.Proof.Rc2.X86.Stream.Update.oA s₀) (VG.Proof.Rc2.X86.Stream.Update.O s₀) = Spec.Rc2.bytesAt s₆.mem (VG.Proof.Rc2.X86.Stream.Update.oA s₀) (VG.Proof.Rc2.X86.Stream.Update.p s₀) ++
        Spec.Rc2.bytesAt s₆.mem (VG.Proof.Rc2.X86.Stream.Update.oA s₀ + BitVec.ofNat 64 (VG.Proof.Rc2.X86.Stream.Update.p s₀)) (VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀) := by
      rw [← Proof.Rc2.bytesAt_add, Nat.add_sub_cancel' hpO]
    have e₁ : Spec.Rc2.bytesAt s₆.mem (VG.Proof.Rc2.X86.Stream.Update.oA s₀) (VG.Proof.Rc2.X86.Stream.Update.p s₀) =
        Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136) (VG.Proof.Rc2.X86.Stream.Update.p s₀) := by
      rw [Proof.Rc2.bytesAt_frame f₆ _ _ (by omega) (sing ((hp.c_o.sub_left (pc pendDst)).sub_right outA).symm),
        Proof.Rc2.bytesAt_frame f₄ _ _ (by omega) (sing (Offset.base_disjoint _ (by omega) (by omega))), b₂,
        Proof.Rc2.bytesAt_frame hf _ _ (by omega) (sing (hp.c_s.sub_left (pc pendSrc)))]
    have e₂ : Spec.Rc2.bytesAt s₆.mem (VG.Proof.Rc2.X86.Stream.Update.oA s₀ + BitVec.ofNat 64 (VG.Proof.Rc2.X86.Stream.Update.p s₀)) (VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀) =
        Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.dA s₀) (VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀) := by
      rw [Proof.Rc2.bytesAt_frame f₆ _ _ (by omega) (sing ((hp.c_o.sub_left (pc pendDst)).sub_right outB).symm),
        b₄, Proof.Rc2.bytesAt_frame f₂ _ _ (by omega) (sing ((hp.d_o.sub_left datA).sub_right outA)),
        Proof.Rc2.bytesAt_frame hf _ _ (by omega) (sing (hp.d_s.sub_left datA))]
    rw [hsplit, e₁, e₂]
  · -- The pending block: the rest of the data.
    rcases Nat.eq_zero_or_pos ((VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8) with h0 | h0
    · rw [h0]; rfl
    rw [b₆, hSp h0, Proof.Rc2.bytesAt_frame f₄ _ _ (by omega) (sing ((hp.d_o.sub_left datB).sub_right outB)),
      Proof.Rc2.bytesAt_frame f₂ _ _ (by omega) (sing ((hp.d_o.sub_left datB).sub_right outA)),
      Proof.Rc2.bytesAt_frame hf _ _ (by omega) (sing (hp.d_s.sub_left datB))]

end VG.Proof.Rc2.X86.Stream.Update

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Stream.Verified`. -/
section

section

section

/-!
# Streaming RC2-CBC on x86 (32-bit): everything before the call

The state before the call of the CBC function (`Mid`): the copies done, and
its arguments in `eax`, `ecx`, `edx`, `esi` and `ebx` (`head_ok`).
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

/-- `shr d, n`, and ZF. -/
theorem wp_shrZ {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → s'.zf = some (s.gpr d >>> n == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl) (k _ (Upd.setFlags _ _ _ _ _ _ _) rfl)

theorem shr3 (x : BitVec 32) : x >>> 3 = BitVec.ofNat 32 (x.toNat / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- The state before the call, from the entry state `s₀`. -/
structure Mid (s₀ s : State) : Prop where
  common : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s
  ebx : s.gpr .ebx = VG.Proof.Rc2.X86.Stream.Update.scr s₀
  eax : s.gpr .eax = VG.Proof.Rc2.X86.Stream.Update.ctx s₀
  ecx : s.gpr .ecx = VG.Proof.Rc2.X86.Stream.Update.ctx s₀ + 128
  edx : s.gpr .edx = VG.Proof.Rc2.X86.Stream.Update.op s₀
  esi : s.gpr .esi = BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.O s₀ / 8)
  zf : s.zf = some (decide (VG.Proof.Rc2.X86.Stream.Update.O s₀ = 0))
  short : VG.Proof.Rc2.X86.Stream.Update.O s₀ = 0 →
    Spec.Rc2.bytesAt s.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136) (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) =
      Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136) (VG.Proof.Rc2.X86.Stream.Update.p s₀) ++
        Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.dA s₀) (VG.Proof.Rc2.X86.Stream.Update.len s₀)
  out : VG.Proof.Rc2.X86.Stream.Update.O s₀ ≠ 0 →
    Spec.Rc2.bytesAt s.mem (VG.Proof.Rc2.X86.Stream.Update.oA s₀) (VG.Proof.Rc2.X86.Stream.Update.O s₀) =
      Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136) (VG.Proof.Rc2.X86.Stream.Update.p s₀) ++
        Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.dA s₀) (VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀)
  pend : VG.Proof.Rc2.X86.Stream.Update.O s₀ ≠ 0 →
    Spec.Rc2.bytesAt s.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136) ((VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8) =
      Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.dA s₀ + BitVec.ofNat 64 (VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀)) ((VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8)

theorem cbcArgs_ok {s₀ s : State} (hp : VG.Proof.Rc2.X86.Stream.Update.Pre s₀) (hc : VG.Proof.Rc2.X86.Stream.Update.Common s₀ s) {Q : State → Prop}
    (hQ : ∀ t, VG.Proof.Rc2.X86.Stream.Update.Common s₀ t → t.mem = s.mem → t.gpr .ebx = VG.Proof.Rc2.X86.Stream.Update.scr s₀ → t.gpr .eax = VG.Proof.Rc2.X86.Stream.Update.ctx s₀ →
      t.gpr .ecx = VG.Proof.Rc2.X86.Stream.Update.ctx s₀ + 128 → t.gpr .edx = VG.Proof.Rc2.X86.Stream.Update.op s₀ → t.gpr .esi = BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.O s₀ / 8) →
      t.zf = some (decide (VG.Proof.Rc2.X86.Stream.Update.O s₀ = 0)) → Q t) :
    WP isa (.block cbcArgs) s Q := by
  have hOe := hp.O_eq
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp hc (i := 6) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp c₁ (i := 0) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine wp_mov fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_addi fun s₄ u₄ => ?_
  have c₄ := c₃.upd u₄ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp c₄ (i := 4) (by decide) fun s₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Update.wp_arg hp c₅ (i := 5) (by decide) fun s₆ u₆ => ?_
  have c₆ := c₅.upd u₆ (by decide) (by decide) (by decide)
  refine VG.Proof.Rc2.X86.Stream.Update.wp_shrZ ⟨by decide, by decide⟩ fun s₇ u₇ hz₇ => WP.block_nil ?_
  have esi₇ : s₇.gpr .esi = BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.O s₀ / 8) := by rw [u₇.gpr, u₆.gpr, VG.Proof.Rc2.X86.Stream.Update.shr3]
  refine hQ s₇ (c₆.upd u₇ (by decide) (by decide) (by decide))
    (by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr])
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr])
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]) esi₇ ?_
  have hOlt : VG.Proof.Rc2.X86.Stream.Update.O s₀ < 2 ^ 32 := (VG.X86.arg s₀ 5).isLt
  rw [hz₇, ← u₇.gpr, esi₇, ofNat_beq_zero (by omega)]
  exact congrArg some (decide_eq_decide.mpr (by omega))

theorem head_ok {s₀ : State} (hp : VG.Proof.Rc2.X86.Stream.Update.Pre s₀) : WP isa head s₀ (VG.Proof.Rc2.X86.Stream.Update.Mid s₀) := by
  refine WP.seq (VG.Proof.Rc2.X86.Stream.Update.entry_ok hp fun s c f hz => ?_)
  refine WP.seq (WP.mono (Q := fun (t : State) => VG.Proof.Rc2.X86.Stream.Update.Common s₀ t ∧
      (VG.Proof.Rc2.X86.Stream.Update.O s₀ = 0 → Spec.Rc2.bytesAt t.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136) (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) =
        Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136) (VG.Proof.Rc2.X86.Stream.Update.p s₀) ++
          Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.dA s₀) (VG.Proof.Rc2.X86.Stream.Update.len s₀)) ∧
      (VG.Proof.Rc2.X86.Stream.Update.O s₀ ≠ 0 → Spec.Rc2.bytesAt t.mem (VG.Proof.Rc2.X86.Stream.Update.oA s₀) (VG.Proof.Rc2.X86.Stream.Update.O s₀) =
        Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136) (VG.Proof.Rc2.X86.Stream.Update.p s₀) ++
          Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.dA s₀) (VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀)) ∧
      (VG.Proof.Rc2.X86.Stream.Update.O s₀ ≠ 0 → Spec.Rc2.bytesAt t.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136) ((VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8) =
        Spec.Rc2.bytesAt s₀.mem (VG.Proof.Rc2.X86.Stream.Update.dA s₀ + BitVec.ofNat 64 (VG.Proof.Rc2.X86.Stream.Update.O s₀ - VG.Proof.Rc2.X86.Stream.Update.p s₀)) ((VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8)))
    (WP.ite _ hz (fun h => ?_) (fun h => ?_)) fun t ⟨ct, h₁, h₂, h₃⟩ => VG.Proof.Rc2.X86.Stream.Update.cbcArgs_ok hp ct
      fun u cu mu ebx eax ecx edx esi zf =>
        ⟨cu, ebx, eax, ecx, edx, esi, zf, fun h => mu ▸ h₁ h, fun h => mu ▸ h₂ h, fun h => mu ▸ h₃ h⟩)
  · have h0 : VG.Proof.Rc2.X86.Stream.Update.O s₀ = 0 := by simpa using h
    exact VG.Proof.Rc2.X86.Stream.Update.short_ok hp h0 c f fun s' c' b => ⟨c', fun _ => b, fun h => absurd h0 h, fun h => absurd h0 h⟩
  · have h0 : VG.Proof.Rc2.X86.Stream.Update.O s₀ ≠ 0 := by simpa using h
    exact VG.Proof.Rc2.X86.Stream.Update.long_ok hp h0 c f fun s' c' b₁ b₂ => ⟨c', fun h => absurd h h0, fun _ => b₁, fun _ => b₂⟩

end VG.Proof.Rc2.X86.Stream.Update

end

/-!
# Streaming RC2-CBC on x86 (32-bit): the call of the CBC function

The call of the verified CBC function on the blocks at `out` (`cbcCall_ok`),
from the state before it (`Mid`), in a frame of its arguments.
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

def cbcName : Spec.Rc2.Direction → String
  | .encrypt => "vg_rc2_cbc_encrypt"
  | .decrypt => "vg_rc2_cbc_decrypt"

/-- The registers pushed as the callee's arguments. -/
abbrev rs5 : List Reg := [.ebx, .esi, .edx, .ecx, .eax]

theorem cbcCall_eq (d : Spec.Rc2.Direction) :
    cbcCall d = .frame (.push VG.Proof.Rc2.X86.Stream.Update.rs5) (.call (VG.Proof.Rc2.X86.Stream.Update.cbcName d) (Impl.Rc2.X86.Cbc.cbc d)) (.pop .eax 5) := by
  cases d <;> rfl

theorem cbc_nosp (d : Spec.Rc2.Direction) : NoSp (Impl.Rc2.X86.Cbc.cbc d) := by
  apply NoSp.of_all
  cases d
  · change Impl.Rc2.X86.Cbc.encrypt.allInstrs _ = true
    lit_decide
  · change Impl.Rc2.X86.Cbc.decrypt.allInstrs _ = true
    lit_decide

theorem cbc_stack (d : Spec.Rc2.Direction) : stackUse (Impl.Rc2.X86.Cbc.cbc d) = 16 := by
  cases d <;> rfl

/-- The regions the CBC function reads (beyond those it writes), and writes. -/
def callRd (s₀ s : State) : List Region :=
  [⟨(VG.Proof.Rc2.X86.Stream.Update.ctx s₀).setWidth 64, 128⟩, ⟨argAddr (pushed VG.Proof.Rc2.X86.Stream.Update.rs5 s).callEntry 0, 20⟩]
def callWr (s₀ : State) : List Region :=
  [⟨(VG.Proof.Rc2.X86.Stream.Update.ctx s₀ + 128).setWidth 64, 8⟩, ⟨VG.Proof.Rc2.X86.Stream.Update.oA s₀, 8 * (VG.Proof.Rc2.X86.Stream.Update.O s₀ / 8)⟩, ⟨VG.Proof.Rc2.X86.Stream.Update.sA s₀, 512⟩]

theorem iv_eq {s₀ : State} (hp : VG.Proof.Rc2.X86.Stream.Update.Pre s₀) : (VG.Proof.Rc2.X86.Stream.Update.ctx s₀ + 128).setWidth 64 = VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 128 :=
  addr_eq (x := VG.Proof.Rc2.X86.Stream.Update.ctx s₀) (k := 128) (by have := hp.c_fit; omega)

section
variable {s₀ s : State} (hp : VG.Proof.Rc2.X86.Stream.Update.Pre s₀) (hm : VG.Proof.Rc2.X86.Stream.Update.Mid s₀ s)
include hp hm

theorem callEntry_args :
    VG.X86.arg (pushed VG.Proof.Rc2.X86.Stream.Update.rs5 s).callEntry 0 = VG.Proof.Rc2.X86.Stream.Update.ctx s₀ ∧ VG.X86.arg (pushed VG.Proof.Rc2.X86.Stream.Update.rs5 s).callEntry 1 = VG.Proof.Rc2.X86.Stream.Update.ctx s₀ + 128 ∧
      VG.X86.arg (pushed VG.Proof.Rc2.X86.Stream.Update.rs5 s).callEntry 2 = VG.Proof.Rc2.X86.Stream.Update.op s₀ ∧
      VG.X86.arg (pushed VG.Proof.Rc2.X86.Stream.Update.rs5 s).callEntry 3 = BitVec.ofNat 32 (VG.Proof.Rc2.X86.Stream.Update.O s₀ / 8) ∧
      VG.X86.arg (pushed VG.Proof.Rc2.X86.Stream.Update.rs5 s).callEntry 4 = VG.Proof.Rc2.X86.Stream.Update.scr s₀ := by
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hm.common.esp]; have := hp.sp_lo; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ VG.Proof.Rc2.X86.Stream.Update.rs5 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [callEntry_arg fit hrs (by simp)]
  · exact hm.eax
  · exact hm.ecx
  · exact hm.edx
  · exact hm.esi
  · exact hm.ebx

omit hp in
theorem callEntry_sp : (pushed VG.Proof.Rc2.X86.Stream.Update.rs5 s).callEntry.gpr .esp = VG.Proof.Rc2.X86.Stream.Update.E s₀ - BitVec.ofNat 32 24 := by
  rw [callEntry_esp', hm.common.esp]; rfl

omit hp in
theorem callEntry_argAddr : argAddr (pushed VG.Proof.Rc2.X86.Stream.Update.rs5 s).callEntry 0 = (VG.Proof.Rc2.X86.Stream.Update.E s₀ - BitVec.ofNat 32 20).setWidth 64 := by
  rw [callEntry_argAddr0, hm.common.esp]; rfl

theorem callPre_ok (d : Spec.Rc2.Direction) :
    VG.X86.CallPre (Cbc.contract d) VG.Proof.Rc2.X86.Stream.Update.rs5 (VG.Proof.Rc2.X86.Stream.Update.callRd s₀ s) (VG.Proof.Rc2.X86.Stream.Update.callWr s₀) s := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := VG.Proof.Rc2.X86.Stream.Update.callEntry_args hp hm
  have eSp := VG.Proof.Rc2.X86.Stream.Update.callEntry_sp hm
  have eA := VG.Proof.Rc2.X86.Stream.Update.callEntry_argAddr hm
  have hOe := hp.O_eq
  have hlo := hp.sp_lo
  have hcf := hp.c_fit
  have hof := hp.o_fit
  have hEf := hp.sp_fit
  have hOlt : VG.Proof.Rc2.X86.Stream.Update.O s₀ < 2 ^ 32 := (VG.X86.arg s₀ 5).isLt
  have e8 : 8 * (VG.Proof.Rc2.X86.Stream.Update.O s₀ / 8) = VG.Proof.Rc2.X86.Stream.Update.O s₀ := by omega
  have ivE := VG.Proof.Rc2.X86.Stream.Update.iv_eq hp
  have hesp : s.gpr .esp = VG.Proof.Rc2.X86.Stream.Update.E s₀ := hm.common.esp
  -- The stack the frame and the callee use.
  have kA : Region.Sub ⟨(VG.Proof.Rc2.X86.Stream.Update.E s₀ - BitVec.ofNat 32 20).setWidth 64, 20⟩ (VG.Proof.Rc2.X86.Stream.Update.stkR s₀) := below_sub (by decide) hlo
  have kR : Region.Sub ⟨(VG.Proof.Rc2.X86.Stream.Update.E s₀ - BitVec.ofNat 32 24).setWidth 64, 4⟩ (VG.Proof.Rc2.X86.Stream.Update.stkR s₀) := by
    have := below_inner (sp := VG.Proof.Rc2.X86.Stream.Update.E s₀) (a := 4) (b := 40) (k := 20) (by omega) hlo
    rw [show VG.Proof.Rc2.X86.Stream.Update.E s₀ - BitVec.ofNat 32 24 = VG.Proof.Rc2.X86.Stream.Update.E s₀ - BitVec.ofNat 32 20 - BitVec.ofNat 32 4 by
      rw [← VG.Offset.sub_add_eq]; rfl]
    exact this
  have kS : Region.Sub (below (VG.Proof.Rc2.X86.Stream.Update.E s₀ - BitVec.ofNat 32 24) 16) (VG.Proof.Rc2.X86.Stream.Update.stkR s₀) := below_inner (by omega) hlo
  have ivS : Region.Sub ⟨(VG.Proof.Rc2.X86.Stream.Update.ctx s₀ + 128).setWidth 64, 8⟩ (VG.Proof.Rc2.X86.Stream.Update.ctxR s₀) := by rw [ivE]; exact Pre.iv_sub
  have oS : Region.Sub ⟨VG.Proof.Rc2.X86.Stream.Update.oA s₀, 8 * (VG.Proof.Rc2.X86.Stream.Update.O s₀ / 8)⟩ (VG.Proof.Rc2.X86.Stream.Update.oR s₀) := by rw [e8]; exact fun _ h => h
  have bS : Region.Sub ⟨VG.Proof.Rc2.X86.Stream.Update.sA s₀, 512⟩ (VG.Proof.Rc2.X86.Stream.Update.scR s₀) := Region.sub_prefix (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [Cbc.contract, VG.Proof.Rc2.X86.Stream.Update.callRd, VG.Proof.Rc2.X86.Stream.Update.callWr, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, eA, eSp, addr32]
    refine ⟨trivial, by rw [toNat_ofNat_lt (by omega)], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [ivE]; exact Pre.sch_iv
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.c_o.sub_left Pre.sch_sub).sub_right oS
    · exact (hp.c_s.sub_left Pre.sch_sub).sub_right bS
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.c_o.sub_left ivS).sub_right oS
    · exact (hp.c_s.sub_left ivS).sub_right bS
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.o_s.sub_left oS).sub_right bS
    · exact (hp.k_c.sub_left kA).sub_right ivS
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.k_o.sub_left kA).sub_right oS
    · exact (hp.k_s.sub_left kA).sub_right bS
    · exact (hp.k_c.sub_left kR).sub_right ivS
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.k_o.sub_left kR).sub_right oS
    · exact (hp.k_s.sub_left kR).sub_right bS
    · exact (hp.k_c.sub_left kS).sub_right Pre.sch_sub
    · exact (hp.k_c.sub_left kS).sub_right ivS
    · rw [toNat_ofNat_lt (by omega)]; exact (hp.k_o.sub_left kS).sub_right oS
    · exact (hp.k_s.sub_left kS).sub_right bS
    · omega
    · show (VG.Proof.Rc2.X86.Stream.Update.ctx s₀ + BitVec.ofNat 32 128).toNat + 8 ≤ _
      rw [VG.Proof.Rc2.X86.Stream.toNat_add_ofNat (by omega)]; omega
    · have := hp.s_fit; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; omega
    · rw [toNat_ofNat_lt (by omega)]; omega
  · have wr : s.wr = [VG.Proof.Rc2.X86.Stream.Update.ctxR s₀, VG.Proof.Rc2.X86.Stream.Update.oR s₀, VG.Proof.Rc2.X86.Stream.Update.scR s₀] := hm.common.wr.trans hp.wr
    refine Covers.of_sub fun r hr => ?_
    simp only [VG.Proof.Rc2.X86.Stream.Update.callRd, VG.Proof.Rc2.X86.Stream.Update.callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨VG.Proof.Rc2.X86.Stream.Update.ctxR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
    · refine ⟨below (s.gpr .esp) (4 * rs5.length), by simp, 0, ?_, by simp⟩
      rw [BitVec.add_zero, callEntry_argAddr0]
    · exact ⟨VG.Proof.Rc2.X86.Stream.Update.ctxR s₀, by simp [wr], 128, ivE, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨VG.Proof.Rc2.X86.Stream.Update.oR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact ⟨VG.Proof.Rc2.X86.Stream.Update.scR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩
  · have wr : s.wr = [VG.Proof.Rc2.X86.Stream.Update.ctxR s₀, VG.Proof.Rc2.X86.Stream.Update.oR s₀, VG.Proof.Rc2.X86.Stream.Update.scR s₀] := hm.common.wr.trans hp.wr
    refine Covers.of_sub fun r hr => ?_
    simp only [VG.Proof.Rc2.X86.Stream.Update.callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.Rc2.X86.Stream.Update.ctxR s₀, by simp [wr], 128, ivE, Nat.le_of_ble_eq_true rfl⟩
    · exact ⟨VG.Proof.Rc2.X86.Stream.Update.oR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, by simp only; omega⟩
    · exact ⟨VG.Proof.Rc2.X86.Stream.Update.scR s₀, by simp [wr], 0, (BitVec.add_zero _).symm, Nat.le_of_ble_eq_true rfl⟩

/-- The call of the CBC function on the `O / 8` blocks at `out`: it writes only the
chaining value, `out`, its scratch space and the stack below `esp`. -/
theorem cbcCall_ok (d : Spec.Rc2.Direction) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [VG.Proof.Rc2.X86.Stream.Update.ivR s₀, VG.Proof.Rc2.X86.Stream.Update.oR s₀, ⟨VG.Proof.Rc2.X86.Stream.Update.sA s₀, 512⟩, VG.Proof.Rc2.X86.Stream.Update.stkR s₀] s.mem s'.mem →
      Spec.Rc2.blocksAt s'.mem (VG.Proof.Rc2.X86.Stream.Update.oA s₀) (VG.Proof.Rc2.X86.Stream.Update.O s₀ / 8) = (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀)) d
        (Spec.Rc2.blockAt s.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 128)) (Spec.Rc2.blocksAt s.mem (VG.Proof.Rc2.X86.Stream.Update.oA s₀) (VG.Proof.Rc2.X86.Stream.Update.O s₀ / 8))).1 →
      Spec.Rc2.blockAt s'.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 128) =
        (Spec.Rc2.cbc (Spec.Rc2.scheduleAt s.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀)) d
          (Spec.Rc2.blockAt s.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 128)) (Spec.Rc2.blocksAt s.mem (VG.Proof.Rc2.X86.Stream.Update.oA s₀) (VG.Proof.Rc2.X86.Stream.Update.O s₀ / 8))).2 →
      Q s') :
    WP isa (cbcCall d) s Q := by
  obtain ⟨a0, a1, a2, a3, a4⟩ := VG.Proof.Rc2.X86.Stream.Update.callEntry_args hp hm
  have hlo := hp.sp_lo
  have hOe := hp.O_eq
  have hOlt : VG.Proof.Rc2.X86.Stream.Update.O s₀ < 2 ^ 32 := (VG.X86.arg s₀ 5).isLt
  have e8 : 8 * (VG.Proof.Rc2.X86.Stream.Update.O s₀ / 8) = VG.Proof.Rc2.X86.Stream.Update.O s₀ := by omega
  have ivE := VG.Proof.Rc2.X86.Stream.Update.iv_eq hp
  have hesp : s.gpr .esp = VG.Proof.Rc2.X86.Stream.Update.E s₀ := hm.common.esp
  have fit : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [hesp]; simp only [List.length_cons, List.length_nil]; omega
  have hrs : Reg.esp ∉ VG.Proof.Rc2.X86.Stream.Update.rs5 := by decide
  have kE : Region.Sub (below (s.gpr .esp) (4 * rs5.length + 4)) (VG.Proof.Rc2.X86.Stream.Update.stkR s₀) := by
    rw [hesp]; exact below_sub (by decide) hlo
  have oS : Region.Sub ⟨VG.Proof.Rc2.X86.Stream.Update.oA s₀, 8 * (VG.Proof.Rc2.X86.Stream.Update.O s₀ / 8)⟩ (VG.Proof.Rc2.X86.Stream.Update.oR s₀) := by rw [e8]; exact fun _ h => h
  have sing {r r' : Region} (h : r.Disjoint r') : ∀ x ∈ [r'], r.Disjoint x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact h
  rw [VG.Proof.Rc2.X86.Stream.Update.cbcCall_eq]
  refine WP.callWith (k := Cbc.contract d) (fun s h => Cbc.cbc_body_correct d s h) (VG.Proof.Rc2.X86.Stream.Update.cbc_nosp d) (by simp)
    hrs (by rw [VG.Proof.Rc2.X86.Stream.Update.cbc_stack, hesp]; simp only [List.length_cons, List.length_nil]; omega)
    (VG.Proof.Rc2.X86.Stream.Update.callPre_ok hp hm d) fun s' rd wr cs f ⟨s₂, m₂, post⟩ => ?_
  have ce := callEntry_frame fit hrs
  simp only [Cbc.contract, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, m₂, addr32,
    toNat_ofNat_lt (show VG.Proof.Rc2.X86.Stream.Update.O s₀ / 8 < 2 ^ 32 by omega), ivE] at post
  have sch : Spec.Rc2.scheduleAt (pushed VG.Proof.Rc2.X86.Stream.Update.rs5 s).callEntry.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀) = Spec.Rc2.scheduleAt s.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀) :=
    Proof.Rc2.scheduleAt_frame ce _ (sing ((hp.k_c.sub_left kE).sub_right Pre.sch_sub).symm)
  have iv : Spec.Rc2.blockAt (pushed VG.Proof.Rc2.X86.Stream.Update.rs5 s).callEntry.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 128) =
      Spec.Rc2.blockAt s.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 128) :=
    Proof.Rc2.blockAt_frame ce _ (sing ((hp.k_c.sub_left kE).sub_right Pre.iv_sub).symm)
  have out : Spec.Rc2.blocksAt (pushed VG.Proof.Rc2.X86.Stream.Update.rs5 s).callEntry.mem (VG.Proof.Rc2.X86.Stream.Update.oA s₀) (VG.Proof.Rc2.X86.Stream.Update.O s₀ / 8) =
      Spec.Rc2.blocksAt s.mem (VG.Proof.Rc2.X86.Stream.Update.oA s₀) (VG.Proof.Rc2.X86.Stream.Update.O s₀ / 8) :=
    Proof.Rc2.blocksAt_frame ce _ _ (sing ((hp.k_o.sub_left kE).sub_right oS).symm)
  rw [sch, iv, out] at post
  refine hQ s' rd wr cs (f.sub fun r hr => ?_) post.1 post.2
  simp only [VG.Proof.Rc2.X86.Stream.Update.callWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨VG.Proof.Rc2.X86.Stream.Update.ivR s₀, by simp, by rw [ivE]; exact fun _ h => h⟩
  · exact ⟨VG.Proof.Rc2.X86.Stream.Update.oR s₀, by simp, oS⟩
  · exact ⟨⟨VG.Proof.Rc2.X86.Stream.Update.sA s₀, 512⟩, by simp, fun _ h => h⟩
  · refine ⟨VG.Proof.Rc2.X86.Stream.Update.stkR s₀, by simp, ?_⟩
    rw [VG.Proof.Rc2.X86.Stream.Update.cbc_stack, hesp]; exact fun _ h => h

end

/-- Our caller's `esi` and `ebx`, from the scratch space at `ebx`. -/
theorem restore_ok {s₀ s : State} (hp : VG.Proof.Rc2.X86.Stream.Update.Pre s₀) (hebx : s.gpr .ebx = VG.Proof.Rc2.X86.Stream.Update.scr s₀)
    (hwr : s.wr = s₀.wr) (h₁ : s.mem.readW (addr (VG.Proof.Rc2.X86.Stream.Update.scr s₀) 512) 32 = s₀.gpr .ebx)
    (h₂ : s.mem.readW (addr (VG.Proof.Rc2.X86.Stream.Update.scr s₀) 516) 32 = s₀.gpr .esi) {Q : State → Prop}
    (hQ : ∀ t, t.mem = s.mem → t.gpr .ebx = s₀.gpr .ebx → t.gpr .esi = s₀.gpr .esi →
      (∀ r, r ≠ .ebx → r ≠ .esi → t.gpr r = s.gpr r) → Q t) :
    WP isa (.block restore) s Q := by
  have rin {d : Nat} (hd : d + 4 ≤ 576) : InRegions (s.rd ++ s.wr) (addr (VG.Proof.Rc2.X86.Stream.Update.scr s₀) d) 4 := by
    obtain ⟨r, hr, hc⟩ := hp.sin hwr hd
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [restore]
  refine wp_ldm (o := 516) hebx (rin (d := 516) (by decide)) fun s₁ u₁ => ?_
  refine wp_ldm (o := 512) (B := VG.Proof.Rc2.X86.Stream.Update.scr s₀) (by rw [u₁.other _ (by decide)]; exact hebx)
    (by rw [u₁.rd, u₁.wr]; exact rin (d := 512) (by decide)) fun s₂ u₂ => WP.block_nil ?_
  refine hQ s₂ (by rw [u₂.mem, u₁.mem]) (by rw [u₂.gpr, u₁.mem]; exact h₁)
    (by rw [u₂.other _ (by decide), u₁.gpr]; exact h₂) fun r a b => ?_
  rw [u₂.other _ a, u₁.other _ b]

end VG.Proof.Rc2.X86.Stream.Update

end

section

section

/-!
# Streaming RC2-CBC on x86 (32-bit): the update functions are correct

From the state before the call (`Mid`): with no complete block, the data is
already appended to the pending bytes; otherwise the CBC function runs on
`out`. Then our caller's registers are restored, and `update_post_short` or
`update_post_long` gives the contract's postcondition.
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

theorem update_correct (d : Spec.Rc2.Direction) (s₀ : State) (hs : (VG.Proof.Rc2.X86.Stream.updateContract d).pre s₀) :
    WP isa (update d) s₀ (fun s' => abiPreserved s₀ s' ∧ (VG.Proof.Rc2.X86.Stream.updateContract d).post s₀ s') := by
  have hp := VG.Proof.Rc2.X86.Stream.Update.pre_of hs
  have hOe := hp.O_eq
  have hpl := hp.p_lt
  have hlo := hp.sp_lo
  have hOe' : (VG.X86.arg s₀ 5).toNat = (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) / 8 * 8 := hp.O_eq
  have sing {r r' : Region} (h : r.Disjoint r') : ∀ x ∈ [r'], r.Disjoint x := fun x hx => by
    simp only [List.mem_singleton] at hx; subst hx; exact h
  have retStk : (VG.Proof.Rc2.X86.Stream.Update.retR s₀).Disjoint (VG.Proof.Rc2.X86.Stream.Update.stkR s₀) := by
    show Region.Disjoint ⟨(VG.Proof.Rc2.X86.Stream.Update.E s₀).setWidth 64, 4⟩ ⟨(VG.Proof.Rc2.X86.Stream.Update.E s₀ - BitVec.ofNat 32 40).setWidth 64, 40⟩
    rw [Taint.sub_setWidth hlo]; exact Offset.base_disjoint_below _ (by decide)
  -- What `Common` keeps.
  have sep3 {r : Region} (h₁ : r.Disjoint (VG.Proof.Rc2.X86.Stream.Update.pendR s₀)) (h₂ : r.Disjoint (VG.Proof.Rc2.X86.Stream.Update.oR s₀)) (h₃ : r.Disjoint (VG.Proof.Rc2.X86.Stream.Update.scR s₀)) :
      ∀ x ∈ [VG.Proof.Rc2.X86.Stream.Update.pendR s₀, VG.Proof.Rc2.X86.Stream.Update.oR s₀, VG.Proof.Rc2.X86.Stream.Update.scR s₀], r.Disjoint x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl)
    exacts [h₁, h₂, h₃]
  have schC : ∀ x ∈ [VG.Proof.Rc2.X86.Stream.Update.pendR s₀, VG.Proof.Rc2.X86.Stream.Update.oR s₀, VG.Proof.Rc2.X86.Stream.Update.scR s₀], (VG.Proof.Rc2.X86.Stream.Update.schR s₀).Disjoint x :=
    sep3 Pre.sch_pend (hp.c_o.sub_left Pre.sch_sub) (hp.c_s.sub_left Pre.sch_sub)
  have ivC : ∀ x ∈ [VG.Proof.Rc2.X86.Stream.Update.pendR s₀, VG.Proof.Rc2.X86.Stream.Update.oR s₀, VG.Proof.Rc2.X86.Stream.Update.scR s₀], (VG.Proof.Rc2.X86.Stream.Update.ivR s₀).Disjoint x :=
    sep3 Pre.iv_pend (hp.c_o.sub_left Pre.iv_sub) (hp.c_s.sub_left Pre.iv_sub)
  have retC : ∀ x ∈ [VG.Proof.Rc2.X86.Stream.Update.pendR s₀, VG.Proof.Rc2.X86.Stream.Update.oR s₀, VG.Proof.Rc2.X86.Stream.Update.scR s₀], (VG.Proof.Rc2.X86.Stream.Update.retR s₀).Disjoint x :=
    sep3 (hp.sep_pend _ (by simp)) hp.r_o hp.r_s
  -- What the call keeps.
  have sep4 {r : Region} (h₁ : r.Disjoint (VG.Proof.Rc2.X86.Stream.Update.ivR s₀)) (h₂ : r.Disjoint (VG.Proof.Rc2.X86.Stream.Update.oR s₀))
      (h₃ : r.Disjoint ⟨VG.Proof.Rc2.X86.Stream.Update.sA s₀, 512⟩) (h₄ : r.Disjoint (VG.Proof.Rc2.X86.Stream.Update.stkR s₀)) :
      ∀ x ∈ [VG.Proof.Rc2.X86.Stream.Update.ivR s₀, VG.Proof.Rc2.X86.Stream.Update.oR s₀, ⟨VG.Proof.Rc2.X86.Stream.Update.sA s₀, 512⟩, VG.Proof.Rc2.X86.Stream.Update.stkR s₀], r.Disjoint x := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro x (rfl | rfl | rfl | rfl)
    exacts [h₁, h₂, h₃, h₄]
  have buf : Region.Sub ⟨VG.Proof.Rc2.X86.Stream.Update.sA s₀, 512⟩ (VG.Proof.Rc2.X86.Stream.Update.scR s₀) := Region.sub_prefix (by decide)
  rw [update]
  refine WP.seq (WP.mono (VG.Proof.Rc2.X86.Stream.Update.head_ok hp) fun s hm => ?_)
  have hc := hm.common
  refine WP.seq (WP.ite _ hm.zf (fun h => WP.block_nil ?_) (fun h => ?_))
  · -- No complete block.
    have h0 : VG.Proof.Rc2.X86.Stream.Update.O s₀ = 0 := by simpa using h
    refine VG.Proof.Rc2.X86.Stream.Update.restore_ok hp hm.ebx hc.wr hc.ebx hc.esi fun t mt tb ts to => ⟨⟨?_, ?_⟩, ?_⟩
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact tb
      · exact ts
      · rw [to _ (by decide) (by decide)]; exact hc.edi
      · rw [to _ (by decide) (by decide)]; exact hc.ebp
      · rw [to _ (by decide) (by decide)]; exact hc.esp
    · rw [mt]; exact hc.frame.readW (Region.contains_self _ _) retC (by decide)
    · have post := update_post_short (m := s₀.mem) (m' := t.mem) (ctx := VG.Proof.Rc2.X86.Stream.Update.cA s₀) (data := VG.Proof.Rc2.X86.Stream.Update.dA s₀)
        (out := VG.Proof.Rc2.X86.Stream.Update.oA s₀) (d := d) (p := VG.Proof.Rc2.X86.Stream.Update.p s₀) (len := VG.Proof.Rc2.X86.Stream.Update.len s₀) (by omega)
        (by rw [mt]; exact Proof.Rc2.scheduleAt_frame hc.frame _ schC)
        (by rw [mt]; exact Proof.Rc2.blockAt_frame hc.frame _ ivC)
        (by rw [mt]; exact hm.short h0)
      simp only [VG.Proof.Rc2.X86.Stream.updateContract]
      rw [hOe']
      exact post
  · -- The CBC function on `out`.
    have h0 : VG.Proof.Rc2.X86.Stream.Update.O s₀ ≠ 0 := by simpa using h
    refine VG.Proof.Rc2.X86.Stream.Update.cbcCall_ok hp hm d fun s' rd wr cs f c₁ c₂ => ?_
    have word {e : Nat} (he : 512 ≤ e) (he' : e + 4 ≤ 576) :
        s'.mem.readW (addr (VG.Proof.Rc2.X86.Stream.Update.scr s₀) e) 32 = s.mem.readW (addr (VG.Proof.Rc2.X86.Stream.Update.scr s₀) e) 32 := by
      refine f.readW (Region.contains_self _ _) (sep4 ?_ ?_ ?_ ?_) (by decide)
      · exact (hp.c_s.sub_left Pre.iv_sub).symm.sub_left (hp.scr_sub he')
      · exact hp.o_s.symm.sub_left (hp.scr_sub he')
      · rw [hp.scr_addr he']; exact Offset.disjoint_base _ he (by omega)
      · exact hp.k_s.symm.sub_left (hp.scr_sub he')
    refine VG.Proof.Rc2.X86.Stream.Update.restore_ok hp (by rw [cs .ebx (by simp [calleeSaved])]; exact hm.ebx) (wr.trans hc.wr)
      (by rw [word (by decide) (by decide)]; exact hc.ebx) (by rw [word (by decide) (by decide)]; exact hc.esi)
      fun t mt tb ts to => ⟨⟨?_, ?_⟩, ?_⟩
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact tb
      · exact ts
      · rw [to _ (by decide) (by decide), cs _ (by simp [calleeSaved])]; exact hc.edi
      · rw [to _ (by decide) (by decide), cs _ (by simp [calleeSaved])]; exact hc.ebp
      · rw [to _ (by decide) (by decide), cs _ (by simp [calleeSaved])]; exact hc.esp
    · rw [mt, f.readW (Region.contains_self _ _) (sep4 (hp.r_c.sub_right Pre.iv_sub) hp.r_o
        (hp.r_s.sub_right buf) retStk) (by decide)]
      exact hc.frame.readW (Region.contains_self _ _) retC (by decide)
    · have e8 : (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) / 8 * 8 / 8 = (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) / 8 := Nat.mul_div_cancel _ (by decide)
      have pendS : Region.Sub ⟨VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136, (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) % 8⟩ (VG.Proof.Rc2.X86.Stream.Update.pendR s₀) :=
        Region.sub_prefix (by have := Nat.mod_lt (VG.Proof.Rc2.X86.Stream.Update.p s₀ + VG.Proof.Rc2.X86.Stream.Update.len s₀) (by decide : 0 < 8); omega)
      have out := hm.out h0
      have pend := hm.pend h0
      rw [hOe] at out pend c₁ c₂
      rw [e8] at c₁ c₂
      have post := update_post_long (m := s₀.mem) (m₁ := s.mem) (m' := t.mem) (ctx := VG.Proof.Rc2.X86.Stream.Update.cA s₀) (data := VG.Proof.Rc2.X86.Stream.Update.dA s₀)
        (out := VG.Proof.Rc2.X86.Stream.Update.oA s₀) (d := d) (p := VG.Proof.Rc2.X86.Stream.Update.p s₀) (len := VG.Proof.Rc2.X86.Stream.Update.len s₀) hpl (by omega) out
        (Proof.Rc2.scheduleAt_frame hc.frame _ schC) (Proof.Rc2.blockAt_frame hc.frame _ ivC)
        (by
          show Spec.Rc2.bytesAt t.mem (VG.Proof.Rc2.X86.Stream.Update.cA s₀ + BitVec.ofNat 64 136) _ = _
          rw [mt, Proof.Rc2.bytesAt_frame f _ _ (by omega) (sep4
            ((Pre.iv_pend).symm.sub_left pendS) ((hp.c_o.sub_left Pre.pend_sub).sub_left pendS)
            (((hp.c_s.sub_left Pre.pend_sub).sub_left pendS).sub_right buf)
            ((hp.k_c.sub_right Pre.pend_sub).symm.sub_left pendS))]
          exact pend)
        (by
          rw [mt]
          exact Proof.Rc2.scheduleAt_frame f _ (sep4 Pre.sch_iv (hp.c_o.sub_left Pre.sch_sub)
            ((hp.c_s.sub_left Pre.sch_sub).sub_right buf) (hp.k_c.sub_right Pre.sch_sub).symm))
        (by rw [mt]; exact c₁) (by rw [mt]; exact c₂)
      simp only [VG.Proof.Rc2.X86.Stream.updateContract]
      rw [hOe']
      exact post

end VG.Proof.Rc2.X86.Stream.Update

end

/-!
# Streaming RC2-CBC on x86 (32-bit): constant time

The taint analysis proves everything but the call of the CBC function (which
restores registers the analysis then takes for secret), from the public
arguments on the stack (`τ0`); the call is related in both runs by
`RelCT.callWith`, from what the correctness proof knows of the state it is
made from (`Mid`), and the restore of our caller's registers through `ebx`,
public again by correctness.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

/-- The arguments on the stack are public, and only read. -/
def τ0 : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 32 }

theorem τ0_wf {s : State} (f : (s.gpr .esp).toNat + 32 ≤ 2 ^ 32)
    (d : ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s 0, 28⟩ r) :
    VG.X86.Taint.Wf VG.Proof.Rc2.X86.Stream.τ0 s :=
  Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨f, fun r hr => Taint.frame_disjoint (n := 28) (by omega) (d r hr).1 (d r hr).2⟩,
    fun _ h => (List.not_mem_nil h).elim⟩

theorem τ0_agree {s₁ s₂ : State} (f₁ : (s₁.gpr .esp).toNat + 32 ≤ 2 ^ 32)
    (f₂ : (s₂.gpr .esp).toNat + 32 ≤ 2 ^ 32)
    (d₁ : ∀ r ∈ s₁.wr, Region.Disjoint ⟨(s₁.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s₁ 0, 28⟩ r)
    (d₂ : ∀ r ∈ s₂.wr, Region.Disjoint ⟨(s₂.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s₂ 0, 28⟩ r)
    (sp : s₁.gpr .esp = s₂.gpr .esp) (args : ∀ i < 7, VG.X86.arg s₁ i = VG.X86.arg s₂ i) :
    VG.X86.Taint.Agree VG.Proof.Rc2.X86.Stream.τ0 s₁ s₂ := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, VG.Proof.Rc2.X86.Stream.τ0_wf f₁ d₁, VG.Proof.Rc2.X86.Stream.τ0_wf f₂ d₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => sp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Rc2.X86.Stream.τ0, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [VG.Proof.Rc2.X86.Stream.τ0] at hk
    rw [show Taint.depth τ0.stk = 0 from rfl, Nat.zero_add, Taint.argByte_eq f₁ h4 hk,
      Taint.argByte_eq f₂ h4 hk, Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

namespace Update

open VG.Impl.Rc2.X86.Stream

def Rel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  (VG.Proof.Rc2.X86.Stream.updateContract d).pre s₁ ∧ (VG.Proof.Rc2.X86.Stream.updateContract d).pre s₂ ∧ (VG.Proof.Rc2.X86.Stream.updateContract d).pub s₁ s₂

theorem Pre.disj {s : State} (hp : VG.Proof.Rc2.X86.Stream.Update.Pre s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s 0, 28⟩ r := by
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  exacts [⟨hp.r_c, hp.a_c⟩, ⟨hp.r_o, hp.a_o⟩, ⟨hp.r_s, hp.a_s⟩]

theorem rel_agree {d : Spec.Rc2.Direction} {s₁ s₂ : State} (h : VG.Proof.Rc2.X86.Stream.Update.Rel d s₁ s₂) :
    VG.X86.Taint.Agree VG.Proof.Rc2.X86.Stream.τ0 s₁ s₂ :=
  VG.Proof.Rc2.X86.Stream.τ0_agree (VG.Proof.Rc2.X86.Stream.Update.pre_of h.1).sp_fit (VG.Proof.Rc2.X86.Stream.Update.pre_of h.2.1).sp_fit (VG.Proof.Rc2.X86.Stream.Update.pre_of h.1).disj (VG.Proof.Rc2.X86.Stream.Update.pre_of h.2.1).disj h.2.2.1 h.2.2.2

/-- After `head`, in both runs. -/
def MidRel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, VG.Proof.Rc2.X86.Stream.Update.Rel d σ₁ σ₂ ∧ VG.Proof.Rc2.X86.Stream.Update.Mid σ₁ s₁ ∧ VG.Proof.Rc2.X86.Stream.Update.Mid σ₂ s₂

theorem call_ct (d : Spec.Rc2.Direction) :
    RelCT isa (fun s₁ s₂ => VG.Proof.Rc2.X86.Stream.Update.MidRel d s₁ s₂ ∧ isa.eval .e s₁ = some false) (cbcCall d)
      (fun s₁ s₂ => s₁.gpr .ebx = s₂.gpr .ebx) := by
  have ct : RelCT isa (fun s₁ s₂ => VG.Proof.Rc2.X86.Stream.Update.MidRel d s₁ s₂ ∧ isa.eval .e s₁ = some false) (cbcCall d)
      (fun _ _ => True) := by
    rintro s₁ s₂ t₁ t₂ u₁ u₂ ⟨⟨σ₁, σ₂, ⟨h₁, h₂, sp, args⟩, m₁, m₂⟩, -⟩ e₁ e₂
    have hp₁ := VG.Proof.Rc2.X86.Stream.Update.pre_of h₁
    have hp₂ := VG.Proof.Rc2.X86.Stream.Update.pre_of h₂
    obtain ⟨a0, a1, a2, a3, a4⟩ := VG.Proof.Rc2.X86.Stream.Update.callEntry_args hp₁ m₁
    obtain ⟨b0, b1, b2, b3, b4⟩ := VG.Proof.Rc2.X86.Stream.Update.callEntry_args hp₂ m₂
    have rd : VG.Proof.Rc2.X86.Stream.Update.callRd σ₂ s₂ = VG.Proof.Rc2.X86.Stream.Update.callRd σ₁ s₁ := by
      simp only [VG.Proof.Rc2.X86.Stream.Update.callRd, VG.Proof.Rc2.X86.Stream.Update.callEntry_argAddr m₁, VG.Proof.Rc2.X86.Stream.Update.callEntry_argAddr m₂, VG.Proof.Rc2.X86.Stream.Update.ctx, VG.Proof.Rc2.X86.Stream.Update.E, sp, args 0 (by decide)]
    have wr : VG.Proof.Rc2.X86.Stream.Update.callWr σ₂ = VG.Proof.Rc2.X86.Stream.Update.callWr σ₁ := by
      simp only [VG.Proof.Rc2.X86.Stream.Update.callWr, VG.Proof.Rc2.X86.Stream.Update.ctx, VG.Proof.Rc2.X86.Stream.Update.oA, VG.Proof.Rc2.X86.Stream.Update.O, VG.Proof.Rc2.X86.Stream.Update.sA, VG.Proof.Rc2.X86.Stream.Update.op, VG.Proof.Rc2.X86.Stream.Update.scr, args 0 (by decide), args 4 (by decide), args 5 (by decide),
        args 6 (by decide)]
    have ct' : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (cbcCall d) (fun _ _ => True) := by
      rw [VG.Proof.Rc2.X86.Stream.Update.cbcCall_eq]
      apply RelCT.callWith (fun s h => Cbc.cbc_body_correct d s h) (Cbc.cbc_constantTime d) (VG.Proof.Rc2.X86.Stream.Update.callRd σ₁ s₁)
        (VG.Proof.Rc2.X86.Stream.Update.callWr σ₁)
      rintro a b ⟨rfl, rfl⟩
      refine ⟨VG.Proof.Rc2.X86.Stream.Update.callPre_ok hp₁ m₁ d, by rw [← rd, ← wr]; exact VG.Proof.Rc2.X86.Stream.Update.callPre_ok hp₂ m₂ d, ?_, ?_, ?_⟩
      · rw [m₁.common.esp, m₂.common.esp]; exact sp
      · simp only [State.withRegions_gpr, VG.Proof.Rc2.X86.Stream.Update.callEntry_sp m₁, VG.Proof.Rc2.X86.Stream.Update.callEntry_sp m₂, VG.Proof.Rc2.X86.Stream.Update.E, sp]
      · intro i hi
        simp only [arg_withRegions]
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
        · rw [a0, b0, VG.Proof.Rc2.X86.Stream.Update.ctx, VG.Proof.Rc2.X86.Stream.Update.ctx, args 0 (by decide)]
        · rw [a1, b1, VG.Proof.Rc2.X86.Stream.Update.ctx, VG.Proof.Rc2.X86.Stream.Update.ctx, args 0 (by decide)]
        · rw [a2, b2, VG.Proof.Rc2.X86.Stream.Update.op, VG.Proof.Rc2.X86.Stream.Update.op, args 4 (by decide)]
        · rw [a3, b3, VG.Proof.Rc2.X86.Stream.Update.O, VG.Proof.Rc2.X86.Stream.Update.O, args 5 (by decide)]
        · rw [a4, b4, VG.Proof.Rc2.X86.Stream.Update.scr, VG.Proof.Rc2.X86.Stream.Update.scr, args 6 (by decide)]
    exact ct' _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  refine (ct.wpDep (F := fun (σ s' : State) => s'.gpr .ebx = σ.gpr .ebx) fun s₁ s₂ h => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨⟨σ₁, σ₂, ⟨h₁, h₂, -⟩, m₁, m₂⟩, -⟩ := h
    exact ⟨VG.Proof.Rc2.X86.Stream.Update.cbcCall_ok (VG.Proof.Rc2.X86.Stream.Update.pre_of h₁) m₁ d fun s' _ _ cs _ _ _ => cs .ebx (by simp [calleeSaved]),
      VG.Proof.Rc2.X86.Stream.Update.cbcCall_ok (VG.Proof.Rc2.X86.Stream.Update.pre_of h₂) m₂ d fun s' _ _ cs _ _ _ => cs .ebx (by simp [calleeSaved])⟩
  · rintro s₁' s₂' ⟨-, s₁, s₂, ⟨⟨σ₁, σ₂, ⟨-, -, -, args⟩, m₁, m₂⟩, -⟩, e₁, e₂⟩
    rw [e₁, e₂, m₁.ebx, m₂.ebx, VG.Proof.Rc2.X86.Stream.Update.scr, VG.Proof.Rc2.X86.Stream.Update.scr, args 6 (by decide)]

theorem update_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (VG.Proof.Rc2.X86.Stream.updateContract d).pre (VG.Proof.Rc2.X86.Stream.updateContract d).pub (update d) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold update
  have hA : RelCT isa (VG.Proof.Rc2.X86.Stream.Update.Rel d) head (fun _ _ => True) :=
    RelCT.taint (A := taint) VG.Proof.Rc2.X86.Stream.τ0 (fun _ _ h => VG.Proof.Rc2.X86.Stream.Update.rel_agree h) (by taint_decide)
  refine (hA.wpDep (F := VG.Proof.Rc2.X86.Stream.Update.Mid) fun s₁ s₂ (h : VG.Proof.Rc2.X86.Stream.Update.Rel d s₁ s₂) => ⟨VG.Proof.Rc2.X86.Stream.Update.head_ok (VG.Proof.Rc2.X86.Stream.Update.pre_of h.1), VG.Proof.Rc2.X86.Stream.Update.head_ok (VG.Proof.Rc2.X86.Stream.Update.pre_of h.2.1)⟩).seq
    (RelCT.seq (R := fun (s₁ s₂ : State) => s₁.gpr .ebx = s₂.gpr .ebx) ?_ ?_)
  · apply RelCT.ite
    · rintro s₁ s₂ ⟨-, σ₁, σ₂, ⟨-, -, -, args⟩, m₁, m₂⟩
      show s₁.zf = s₂.zf
      rw [m₁.zf, m₂.zf, VG.Proof.Rc2.X86.Stream.Update.O, VG.Proof.Rc2.X86.Stream.Update.O, args 5 (by decide)]
    · apply RelCT.nil
      rintro s₁ s₂ ⟨⟨-, σ₁, σ₂, ⟨-, -, -, args⟩, m₁, m₂⟩, -⟩
      rw [m₁.ebx, m₂.ebx, VG.Proof.Rc2.X86.Stream.Update.scr, VG.Proof.Rc2.X86.Stream.Update.scr, args 6 (by decide)]
    · exact (VG.Proof.Rc2.X86.Stream.Update.call_ct d).mono (fun _ _ h => ⟨h.1.2, h.2⟩) (fun _ _ h => h)
  · exact RelCT.taint (A := taint) (τr [.ebx])
      (fun _ _ h => agree_regs (fun r hr => by rw [List.mem_singleton.mp hr]; exact h)) (by taint_decide)

end Update

end VG.Proof.Rc2.X86.Stream

end

section

/-!
# Streaming RC2-CBC on x86 (32-bit): the shared contracts

The shared contracts (`Proof.Rc2.cbcInitScratchContract`,
`Proof.Rc2.cbcUpdateScratchContract`) let the code write its arguments; `wideInit` and
`wideUpdate` are the per-target contracts with that permission, which imply
the shared ones. `narrow*` drop it again, for the proofs against
`initContract` and `updateContract`.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

/-- `initContract`, with the arguments writable. -/
def wideInit : Contract isa :=
  { VG.Proof.Rc2.X86.Stream.initContract with
    pre := fun s =>
      let key : Region := ⟨(VG.X86.arg s 0).setWidth 64, (VG.X86.arg s 1).toNat⟩
      let iv : Region := ⟨(VG.X86.arg s 3).setWidth 64, (VG.X86.arg s 4).toNat⟩
      let ctx : Region := ⟨(VG.X86.arg s 5).setWidth 64, 144⟩
      let buf : Region := ⟨(VG.X86.arg s 6).setWidth 64, 576⟩
      let args : Region := ⟨argAddr s 0, 28⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) 24
      s.rd = [key, iv] ∧ s.wr = [ctx, buf, args] ∧
        key.Disjoint ctx ∧ key.Disjoint buf ∧ iv.Disjoint ctx ∧ iv.Disjoint buf ∧ ctx.Disjoint buf ∧
        args.Disjoint ctx ∧ args.Disjoint buf ∧ ret.Disjoint ctx ∧ ret.Disjoint buf ∧
        stack.Disjoint key ∧ stack.Disjoint iv ∧ stack.Disjoint ctx ∧ stack.Disjoint buf ∧
        (VG.X86.arg s 0).toNat + (VG.X86.arg s 1).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 3).toNat + (VG.X86.arg s 4).toNat ≤ 2 ^ 32 ∧
        (VG.X86.arg s 5).toNat + 144 ≤ 2 ^ 32 ∧ (VG.X86.arg s 6).toNat + 576 ≤ 2 ^ 32 ∧
        24 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 }

/-- `updateContract d`, with the arguments writable. -/
def wideUpdate (d : Spec.Rc2.Direction) : Contract isa :=
  { VG.Proof.Rc2.X86.Stream.updateContract d with
    pre := fun s =>
      let ctx : Region := ⟨(VG.X86.arg s 0).setWidth 64, 144⟩
      let data : Region := ⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩
      let out : Region := ⟨(VG.X86.arg s 4).setWidth 64, (VG.X86.arg s 5).toNat⟩
      let buf : Region := ⟨(VG.X86.arg s 6).setWidth 64, 576⟩
      let args : Region := ⟨argAddr s 0, 28⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack := below (s.gpr .esp) 40
      s.rd = [data] ∧ s.wr = [ctx, out, buf, args] ∧
        ctx.Disjoint data ∧ ctx.Disjoint out ∧ ctx.Disjoint buf ∧ data.Disjoint out ∧
        data.Disjoint buf ∧ out.Disjoint buf ∧
        args.Disjoint ctx ∧ args.Disjoint out ∧ args.Disjoint buf ∧
        ret.Disjoint ctx ∧ ret.Disjoint out ∧ ret.Disjoint buf ∧
        stack.Disjoint ctx ∧ stack.Disjoint data ∧ stack.Disjoint out ∧ stack.Disjoint buf ∧
        (VG.X86.arg s 0).toNat + 144 ≤ 2 ^ 32 ∧ (VG.X86.arg s 2).toNat + (VG.X86.arg s 3).toNat ≤ 2 ^ 32 ∧
        (VG.X86.arg s 4).toNat + (VG.X86.arg s 5).toNat ≤ 2 ^ 32 ∧ (VG.X86.arg s 6).toNat + 576 ≤ 2 ^ 32 ∧
        40 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 ∧
        (VG.X86.arg s 1).toNat < 8 ∧ (VG.X86.arg s 5).toNat = ((VG.X86.arg s 1).toNat + (VG.X86.arg s 3).toNat) / 8 * 8 }

/-- `init(0x1000, 1, 8, 0x2000, 8, 0x3000, 0x4000)`. -/
def initSat : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x6008 then 1 else if a = 0x600c then 8 else
    if a = 0x6011 then 0x20 else if a = 0x6014 then 8 else if a = 0x6019 then 0x30 else
    if a = 0x601d then 0x40 else 0
  rd := [⟨0x1000, 1⟩, ⟨0x2000, 8⟩]
  wr := [⟨0x3000, 144⟩, ⟨0x4000, 576⟩, ⟨0x6004, 28⟩]

/-- `update(0x1000, 0, 0x2000, 0, 0x3000, 0, 0x4000)`. -/
def updateSat : State where
  gpr r := if r = .esp then 0x6000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6005 then 0x10 else if a = 0x600d then 0x20 else if a = 0x6015 then 0x30 else
    if a = 0x601d then 0x40 else 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩, ⟨0x4000, 576⟩, ⟨0x6004, 28⟩]

syntax "wide_pre " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| wide_pre [$ls,*]) => `(tactic| (
    intro s h
    sig_pre [$ls,*] at h
    sig_split h
    sig_reduce [$ls,*]
    sig_simp [$ls,*] []
    sig_and_intros
    sig_close
    all_goals first
      | with_reducible assumption
      | with_reducible exact Region.Disjoint.symm ‹_›
      | omega
      | (rw [Taint.sub_setWidth (by omega)]
         first
           | with_reducible assumption
           | with_reducible exact Region.Disjoint.symm ‹_›)))

theorem init_implies : wideInit.Implies (Proof.Rc2.cbcInitScratchContract abi 24) where
  pre := by
    wide_pre [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argSlots, argVal, argBytes,
      VG.Proof.Rc2.X86.Stream.wideInit, VG.Proof.Rc2.X86.Stream.initContract, below]
  post := by
    sig_implies_post [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argSlots, argVal, argBytes,
      VG.Proof.Rc2.X86.Stream.wideInit, VG.Proof.Rc2.X86.Stream.initContract, below]
  pub := by
    sig_implies_pub [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argSlots, argVal, argBytes,
      VG.Proof.Rc2.X86.Stream.wideInit, VG.Proof.Rc2.X86.Stream.initContract, below]
  sat := by
    sig_implies_sat [Proof.Rc2.cbcInitScratchContract, Proof.Rc2.cbcInitScratchSig, Spec.Rc2.cbcInitPost, abi, argSlots, argVal, argBytes,
      VG.Proof.Rc2.X86.Stream.wideInit, VG.Proof.Rc2.X86.Stream.initContract, below] [initSat, arg, argAddr, Mem.readW, Mem.read] using VG.Proof.Rc2.X86.Stream.initSat

theorem update_implies (d : Spec.Rc2.Direction) :
    (VG.Proof.Rc2.X86.Stream.wideUpdate d).Implies (Proof.Rc2.cbcUpdateScratchContract abi d 40) where
  pre := by
    wide_pre [Proof.Rc2.cbcUpdateScratchContract, Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost, abi, argSlots, argVal, argBytes,
      VG.Proof.Rc2.X86.Stream.wideUpdate, VG.Proof.Rc2.X86.Stream.updateContract, below]
  post := by
    sig_implies_post [Proof.Rc2.cbcUpdateScratchContract, Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost, abi, argSlots, argVal, argBytes,
      VG.Proof.Rc2.X86.Stream.wideUpdate, VG.Proof.Rc2.X86.Stream.updateContract, below]
  pub := by
    sig_implies_pub [Proof.Rc2.cbcUpdateScratchContract, Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost, abi, argSlots, argVal, argBytes,
      VG.Proof.Rc2.X86.Stream.wideUpdate, VG.Proof.Rc2.X86.Stream.updateContract, below]
  sat := by
    sig_implies_sat [Proof.Rc2.cbcUpdateScratchContract, Proof.Rc2.cbcUpdateScratchSig, Spec.Rc2.cbcUpdatePre, Spec.Rc2.cbcUpdatePost, abi, argSlots, argVal, argBytes,
      VG.Proof.Rc2.X86.Stream.wideUpdate, VG.Proof.Rc2.X86.Stream.updateContract, below] [updateSat, arg, argAddr, Mem.readW, Mem.read] using VG.Proof.Rc2.X86.Stream.updateSat

end VG.Proof.Rc2.X86.Stream

end

section

/-!
# Streaming RC2-CBC on x86 (32-bit): `init` is constant time

As for the updates (`UpdateCT.lean`): the taint analysis proves the checks and
the copy of the IV, `RelCT.callWith` the call of the key expansion, and the
restore of our caller's registers through `ebx`, public again by correctness.
-/

namespace VG.Proof.Rc2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

def Rel (s₁ s₂ : State) : Prop := initContract.pre s₁ ∧ initContract.pre s₂ ∧ initContract.pub s₁ s₂

theorem Pre.disj {s₀ s : State} (hp : VG.Proof.Rc2.X86.Stream.Init.Pre s₀) (hc : VG.Proof.Rc2.X86.Stream.Init.Common s₀ s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s 0, 28⟩ r := by
  have e : argAddr s 0 = argAddr s₀ 0 := by unfold argAddr; rw [hc.esp]
  rw [hc.wr, hp.wr, hc.esp, e]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  exacts [⟨hp.r_c, hp.a_c⟩, ⟨hp.r_s, hp.a_s⟩]

/-- The arguments, from a state whose memory is the entry state's. -/
theorem arg_eq {s₀ s : State} (hc : VG.Proof.Rc2.X86.Stream.Init.Common s₀ s) (hm : s.mem = s₀.mem) (i : Nat) : VG.X86.arg s i = VG.X86.arg s₀ i := by
  unfold VG.X86.arg argAddr; rw [hc.esp, hm]

theorem agree_mid {σ₁ σ₂ s₁ s₂ : State} (h : VG.Proof.Rc2.X86.Stream.Init.Rel σ₁ σ₂) (c₁ : VG.Proof.Rc2.X86.Stream.Init.Common σ₁ s₁) (c₂ : VG.Proof.Rc2.X86.Stream.Init.Common σ₂ s₂)
    (m₁ : s₁.mem = σ₁.mem) (m₂ : s₂.mem = σ₂.mem) : VG.X86.Taint.Agree VG.Proof.Rc2.X86.Stream.τ0 s₁ s₂ := by
  have hp₁ := VG.Proof.Rc2.X86.Stream.Init.pre_of h.1
  have hp₂ := VG.Proof.Rc2.X86.Stream.Init.pre_of h.2.1
  refine VG.Proof.Rc2.X86.Stream.τ0_agree (by rw [c₁.esp]; exact hp₁.sp_fit) (by rw [c₂.esp]; exact hp₂.sp_fit) (hp₁.disj c₁)
    (hp₂.disj c₂) (by rw [c₁.esp, c₂.esp]; exact h.2.2.1) fun i hi => ?_
  rw [VG.Proof.Rc2.X86.Stream.Init.arg_eq c₁ m₁, VG.Proof.Rc2.X86.Stream.Init.arg_eq c₂ m₂]; exact h.2.2.2 i hi

theorem code_eq {σ₁ σ₂ : State} (args : ∀ i < 7, VG.X86.arg σ₁ i = VG.X86.arg σ₂ i) : VG.Proof.Rc2.X86.Stream.Init.code σ₁ = VG.Proof.Rc2.X86.Stream.Init.code σ₂ := by
  simp only [VG.Proof.Rc2.X86.Stream.Init.code, VG.Proof.Rc2.X86.Stream.Init.kl, VG.Proof.Rc2.X86.Stream.Init.eb, VG.Proof.Rc2.X86.Stream.Init.il, args 1 (by decide), args 2 (by decide), args 4 (by decide)]

/-- After the checks and the test of their result. -/
structure Checked (s₀ s : State) : Prop where
  common : VG.Proof.Rc2.X86.Stream.Init.Common s₀ s
  mem : s.mem = s₀.mem
  zf : s.zf = some (decide (VG.Proof.Rc2.X86.Stream.Init.code s₀ = 0))
  ebx : s.gpr .ebx = s₀.gpr .ebx
  esi : s.gpr .esi = s₀.gpr .esi

theorem checked_ok {s₀ : State} (hp : VG.Proof.Rc2.X86.Stream.Init.Pre s₀) :
    WP isa (.seq checks (.block [.alu .test .eax (.reg .eax)])) s₀ (VG.Proof.Rc2.X86.Stream.Init.Checked s₀) := by
  refine WP.seq (VG.Proof.Rc2.X86.Stream.Init.checks_ok hp fun s c m a b e => wp_test fun s₁ f₁ hz => WP.block_nil ?_)
  refine ⟨c.fupd f₁, by rw [f₁.mem, m], ?_, by rw [f₁.gpr]; exact b, by rw [f₁.gpr]; exact e⟩
  rw [hz, a, BitVec.and_self, ofNat_beq_zero (by have := VG.Proof.Rc2.X86.Stream.Init.code_lt s₀; omega)]

/-- Before the call. -/
structure Args (s₀ s : State) : Prop where
  common : VG.Proof.Rc2.X86.Stream.Init.Common s₀ s
  eax : s.gpr .eax = VG.Proof.Rc2.X86.Stream.Init.key s₀
  ecx : s.gpr .ecx = VG.X86.arg s₀ 1
  edx : s.gpr .edx = VG.X86.arg s₀ 2
  esi : s.gpr .esi = VG.Proof.Rc2.X86.Stream.Init.ctx s₀
  ebx : s.gpr .ebx = VG.Proof.Rc2.X86.Stream.Init.scr s₀

def CheckedRel (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, VG.Proof.Rc2.X86.Stream.Init.Rel σ₁ σ₂ ∧ VG.Proof.Rc2.X86.Stream.Init.Checked σ₁ s₁ ∧ VG.Proof.Rc2.X86.Stream.Init.Checked σ₂ s₂

def ArgsRel (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, VG.Proof.Rc2.X86.Stream.Init.Rel σ₁ σ₂ ∧ VG.Proof.Rc2.X86.Stream.Init.code σ₁ = 0 ∧ VG.Proof.Rc2.X86.Stream.Init.Args σ₁ s₁ ∧ VG.Proof.Rc2.X86.Stream.Init.Args σ₂ s₂

theorem args_ct :
    RelCT isa (fun s₁ s₂ => VG.Proof.Rc2.X86.Stream.Init.CheckedRel s₁ s₂ ∧ isa.eval .ne s₁ = some false) (.block initArgs) VG.Proof.Rc2.X86.Stream.Init.ArgsRel := by
  have ct : RelCT isa (fun s₁ s₂ => VG.Proof.Rc2.X86.Stream.Init.CheckedRel s₁ s₂ ∧ isa.eval .ne s₁ = some false) (.block initArgs)
      (fun _ _ => True) := by
    refine RelCT.taint (A := taint) VG.Proof.Rc2.X86.Stream.τ0 (fun s₁ s₂ h => ?_) (by taint_decide)
    obtain ⟨⟨σ₁, σ₂, hσ, k₁, k₂⟩, -⟩ := h
    exact VG.Proof.Rc2.X86.Stream.Init.agree_mid hσ k₁.common k₂.common k₁.mem k₂.mem
  have code0 : ∀ {σ s : State}, VG.Proof.Rc2.X86.Stream.Init.Checked σ s → isa.eval .ne s = some false → VG.Proof.Rc2.X86.Stream.Init.code σ = 0 := fun k z => by
    have : isa.eval .ne _ = _ := congrArg (Option.map (!·)) k.zf
    rw [z] at this
    exact of_decide_eq_true (by revert this; cases decide (VG.Proof.Rc2.X86.Stream.Init.code _ = 0) <;> simp)
  have h : ∀ σ : State × State, RelCT isa (fun s₁ s₂ =>
      (VG.Proof.Rc2.X86.Stream.Init.CheckedRel s₁ s₂ ∧ isa.eval .ne s₁ = some false) ∧ VG.Proof.Rc2.X86.Stream.Init.Rel σ.1 σ.2 ∧ VG.Proof.Rc2.X86.Stream.Init.Checked σ.1 s₁ ∧ VG.Proof.Rc2.X86.Stream.Init.Checked σ.2 s₂ ∧
        VG.Proof.Rc2.X86.Stream.Init.code σ.1 = 0) (.block initArgs) VG.Proof.Rc2.X86.Stream.Init.ArgsRel := fun σ => by
    refine ((ct.mono (fun _ _ h => h.1) (fun _ _ h => h)).wp
      (F₁ := fun (s : State) => VG.Proof.Rc2.X86.Stream.Init.Rel σ.1 σ.2 ∧ VG.Proof.Rc2.X86.Stream.Init.code σ.1 = 0 ∧ VG.Proof.Rc2.X86.Stream.Init.Args σ.1 s) (F₂ := VG.Proof.Rc2.X86.Stream.Init.Args σ.2) fun s₁ s₂ h => ?_).mono
      (fun _ _ h => h) fun _ _ h => ⟨σ.1, σ.2, h.2.1.1, h.2.1.2.1, h.2.1.2.2, h.2.2⟩
    obtain ⟨-, hσ, k₁, k₂, h0⟩ := h
    have hp₁ := VG.Proof.Rc2.X86.Stream.Init.pre_of hσ.1
    have hp₂ := VG.Proof.Rc2.X86.Stream.Init.pre_of hσ.2.1
    have h0' : VG.Proof.Rc2.X86.Stream.Init.code σ.2 = 0 := (VG.Proof.Rc2.X86.Stream.Init.code_eq hσ.2.2.2).symm.trans h0
    exact ⟨VG.Proof.Rc2.X86.Stream.Init.initArgs_ok hp₁ (VG.Proof.Rc2.X86.Stream.Init.code_ok h0).2.2 k₁.common k₁.mem k₁.ebx k₁.esi
        fun t c ea ec ed es eb _ _ _ => ⟨hσ, h0, c, ea, ec, ed, es, eb⟩,
      VG.Proof.Rc2.X86.Stream.Init.initArgs_ok hp₂ (VG.Proof.Rc2.X86.Stream.Init.code_ok h0').2.2 k₂.common k₂.mem k₂.ebx k₂.esi
        fun t c ea ec ed es eb _ _ _ => ⟨c, ea, ec, ed, es, eb⟩⟩
  refine (RelCT.exists_ h).mono (fun s₁ s₂ hh => ?_) (fun _ _ h => h)
  obtain ⟨⟨σ₁, σ₂, hσ, k₁, k₂⟩, z⟩ := hh
  exact ⟨(σ₁, σ₂), ⟨⟨σ₁, σ₂, hσ, k₁, k₂⟩, z⟩, hσ, k₁, k₂, code0 k₁ z⟩

theorem call_ct : RelCT isa VG.Proof.Rc2.X86.Stream.Init.ArgsRel keyCall (fun s₁ s₂ => s₁.gpr .ebx = s₂.gpr .ebx) := by
  rintro s₁ s₂ t₁ t₂ u₁ u₂ ⟨σ₁, σ₂, ⟨h₁, h₂, sp, args⟩, h0, a₁, a₂⟩ e₁ e₂
  have hp₁ := VG.Proof.Rc2.X86.Stream.Init.pre_of h₁
  have hp₂ := VG.Proof.Rc2.X86.Stream.Init.pre_of h₂
  have h0' : VG.Proof.Rc2.X86.Stream.Init.code σ₂ = 0 := (VG.Proof.Rc2.X86.Stream.Init.code_eq args).symm.trans h0
  obtain ⟨hk₁, he₁, -⟩ := VG.Proof.Rc2.X86.Stream.Init.code_ok h0
  obtain ⟨hk₂, he₂, -⟩ := VG.Proof.Rc2.X86.Stream.Init.code_ok h0'
  have pre₁ := VG.Proof.Rc2.X86.Stream.Init.keyCallPre_ok hp₁ hk₁ he₁ a₁.common a₁.eax a₁.ecx a₁.edx a₁.esi a₁.ebx
  have pre₂ := VG.Proof.Rc2.X86.Stream.Init.keyCallPre_ok hp₂ hk₂ he₂ a₂.common a₂.eax a₂.ecx a₂.edx a₂.esi a₂.ebx
  have fit (s : State) (σ : State) (hp : VG.Proof.Rc2.X86.Stream.Init.Pre σ) (c : VG.Proof.Rc2.X86.Stream.Init.Common σ s) : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [c.esp]; simp only [List.length_cons, List.length_nil]; have := hp.sp_lo; omega
  have hrs : Reg.esp ∉ VG.Proof.Rc2.X86.Stream.Init.rs5 := by decide
  have esp : s₁.gpr .esp = s₂.gpr .esp := by rw [a₁.common.esp, a₂.common.esp]; exact sp
  have rd : VG.Proof.Rc2.X86.Stream.Init.callRd σ₂ s₂ = VG.Proof.Rc2.X86.Stream.Init.callRd σ₁ s₁ := by
    simp only [VG.Proof.Rc2.X86.Stream.Init.callRd, callEntry_argAddr0, esp, VG.Proof.Rc2.X86.Stream.Init.keyR, VG.Proof.Rc2.X86.Stream.Init.kA, VG.Proof.Rc2.X86.Stream.Init.kl, VG.Proof.Rc2.X86.Stream.Init.key, args 0 (by decide), args 1 (by decide)]
  have wr : VG.Proof.Rc2.X86.Stream.Init.callWr σ₂ = VG.Proof.Rc2.X86.Stream.Init.callWr σ₁ := by
    simp only [VG.Proof.Rc2.X86.Stream.Init.callWr, VG.Proof.Rc2.X86.Stream.Init.schR, VG.Proof.Rc2.X86.Stream.Init.cA, VG.Proof.Rc2.X86.Stream.Init.sA, VG.Proof.Rc2.X86.Stream.Init.ctx, VG.Proof.Rc2.X86.Stream.Init.scr, args 5 (by decide), args 6 (by decide)]
  have ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) keyCall (fun _ _ => True) := by
    apply RelCT.callWith key_body_correct expandKey_constantTime (VG.Proof.Rc2.X86.Stream.Init.callRd σ₁ s₁) (VG.Proof.Rc2.X86.Stream.Init.callWr σ₁)
    intro a b hab
    rw [hab.1, hab.2]
    refine ⟨pre₁, by rw [← rd, ← wr]; exact pre₂, esp, ?_, ?_⟩
    · simp only [State.withRegions_gpr, callEntry_esp', esp]
    · intro i hi
      simp only [arg_withRegions]
      rw [callEntry_arg (fit _ _ hp₁ a₁.common) hrs (by simpa using hi),
        callEntry_arg (fit _ _ hp₂ a₂.common) hrs (by simpa using hi)]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
      · show s₁.gpr .eax = s₂.gpr .eax; rw [a₁.eax, a₂.eax, VG.Proof.Rc2.X86.Stream.Init.key, VG.Proof.Rc2.X86.Stream.Init.key, args 0 (by decide)]
      · show s₁.gpr .ecx = s₂.gpr .ecx; rw [a₁.ecx, a₂.ecx, args 1 (by decide)]
      · show s₁.gpr .edx = s₂.gpr .edx; rw [a₁.edx, a₂.edx, args 2 (by decide)]
      · show s₁.gpr .esi = s₂.gpr .esi; rw [a₁.esi, a₂.esi, VG.Proof.Rc2.X86.Stream.Init.ctx, VG.Proof.Rc2.X86.Stream.Init.ctx, args 5 (by decide)]
      · show s₁.gpr .ebx = s₂.gpr .ebx; rw [a₁.ebx, a₂.ebx, VG.Proof.Rc2.X86.Stream.Init.scr, VG.Proof.Rc2.X86.Stream.Init.scr, args 6 (by decide)]
  obtain ⟨ht, -, b₁, b₂⟩ := (ct.wp (F₁ := fun (s : State) => s.gpr .ebx = VG.Proof.Rc2.X86.Stream.Init.scr σ₁) (F₂ := fun (s : State) => s.gpr .ebx = VG.Proof.Rc2.X86.Stream.Init.scr σ₂)
    fun a b ⟨ha, hb⟩ => by
      subst ha hb
      exact ⟨VG.Proof.Rc2.X86.Stream.Init.keyCall_ok hp₁ hk₁ he₁ a₁.common a₁.eax a₁.ecx a₁.edx a₁.esi a₁.ebx
          fun s' _ _ cs _ _ => (cs .ebx (by simp [calleeSaved])).trans a₁.ebx,
        VG.Proof.Rc2.X86.Stream.Init.keyCall_ok hp₂ hk₂ he₂ a₂.common a₂.eax a₂.ecx a₂.edx a₂.esi a₂.ebx
          fun s' _ _ cs _ _ => (cs .ebx (by simp [calleeSaved])).trans a₂.ebx⟩) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  exact ⟨ht, show u₁.gpr .ebx = u₂.gpr .ebx by rw [b₁, b₂, VG.Proof.Rc2.X86.Stream.Init.scr, VG.Proof.Rc2.X86.Stream.Init.scr, args 6 (by decide)]⟩

theorem init_constantTime : ConstantTime isa initContract.pre initContract.pub init := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold init
  apply RelCT.assoc
  have hA : RelCT isa VG.Proof.Rc2.X86.Stream.Init.Rel (.seq checks (.block [.alu .test .eax (.reg .eax)])) (fun _ _ => True) :=
    RelCT.taint (A := taint) VG.Proof.Rc2.X86.Stream.τ0 (fun s₁ s₂ h => VG.Proof.Rc2.X86.Stream.Init.agree_mid h (Common.refl _) (Common.refl _) rfl rfl)
      (by taint_decide)
  refine ((hA.wpDep (F := VG.Proof.Rc2.X86.Stream.Init.Checked) fun s₁ s₂ (h : VG.Proof.Rc2.X86.Stream.Init.Rel s₁ s₂) =>
    ⟨VG.Proof.Rc2.X86.Stream.Init.checked_ok (VG.Proof.Rc2.X86.Stream.Init.pre_of h.1), VG.Proof.Rc2.X86.Stream.Init.checked_ok (VG.Proof.Rc2.X86.Stream.Init.pre_of h.2.1)⟩).mono (fun _ _ h => h)
      (Q' := VG.Proof.Rc2.X86.Stream.Init.CheckedRel) fun _ _ h => h.2).seq ?_
  apply RelCT.ite
  · rintro s₁ s₂ ⟨σ₁, σ₂, ⟨-, -, -, args⟩, k₁, k₂⟩
    show s₁.zf.map (!·) = s₂.zf.map (!·)
    rw [k₁.zf, k₂.zf, VG.Proof.Rc2.X86.Stream.Init.code_eq args]
  · exact RelCT.nil fun _ _ _ => trivial
  · unfold initBody
    refine args_ct.seq (call_ct.seq ?_)
    exact RelCT.taint (A := taint) (τr [.ebx])
      (fun _ _ h => agree_regs (fun r hr => by rw [List.mem_singleton.mp hr]; exact h)) (by taint_decide)

end VG.Proof.Rc2.X86.Stream.Init

end

/-!
# Streaming RC2-CBC on x86 (32-bit): `Verified`

`init` and the updates meet `initContract` and `updateContract`, with their
arguments only read; the shared contracts let the code write them too
(`wideInit`, `wideUpdate`), which `Verified.narrowTo` allows, and
`init_implies` and `update_implies` take the proofs to the shared contracts.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

/-! ## `init` -/

def initRd (s : State) : List Region :=
  [⟨(VG.X86.arg s 0).setWidth 64, (VG.X86.arg s 1).toNat⟩, ⟨(VG.X86.arg s 3).setWidth 64, (VG.X86.arg s 4).toNat⟩, ⟨argAddr s 0, 28⟩]
def initWr (s : State) : List Region := [⟨(VG.X86.arg s 5).setWidth 64, 144⟩, ⟨(VG.X86.arg s 6).setWidth 64, 576⟩]

def updateRd (s : State) : List Region := [⟨(VG.X86.arg s 2).setWidth 64, (VG.X86.arg s 3).toNat⟩, ⟨argAddr s 0, 28⟩]
def updateWr (s : State) : List Region :=
  [⟨(VG.X86.arg s 0).setWidth 64, 144⟩, ⟨(VG.X86.arg s 4).setWidth 64, (VG.X86.arg s 5).toNat⟩, ⟨(VG.X86.arg s 6).setWidth 64, 576⟩]

local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [VG.Proof.Rc2.X86.Stream.initContract, VG.Proof.Rc2.X86.Stream.wideInit,
    VG.Proof.Rc2.X86.Stream.updateContract, VG.Proof.Rc2.X86.Stream.wideUpdate,
    VG.Proof.Rc2.X86.Stream.initRd, VG.Proof.Rc2.X86.Stream.initWr,
    VG.Proof.Rc2.X86.Stream.updateRd, VG.Proof.Rc2.X86.Stream.updateWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem wideInit_pre (s : State) (h : wideInit.pre s) : initContract.pre (s.withRegions (VG.Proof.Rc2.X86.Stream.initRd s) (VG.Proof.Rc2.X86.Stream.initWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

theorem wideUpdate_pre (d : Spec.Rc2.Direction) (s : State) (h : (VG.Proof.Rc2.X86.Stream.wideUpdate d).pre s) :
    (VG.Proof.Rc2.X86.Stream.updateContract d).pre (s.withRegions (VG.Proof.Rc2.X86.Stream.updateRd s) (VG.Proof.Rc2.X86.Stream.updateWr s)) := by
  obtain ⟨_, _, h⟩ := h
  narrow
  exact ⟨trivial, trivial, h⟩

theorem init_verified : Verified target Impl.Rc2.X86.Stream.init (Proof.Rc2.cbcInitScratchContract abi 24) := by
  have hsat := init_implies.sat_left
  have narrowSat : ∃ s, initContract.pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, VG.Proof.Rc2.X86.Stream.wideInit_pre s hs⟩
  apply Verified.of_implies _ VG.Proof.Rc2.X86.Stream.init_implies
  refine Verified.narrowTo
    (Verified.of_correct (fun s hs => Init.init_correct s hs) Init.init_constantTime (.refl narrowSat))
    VG.Proof.Rc2.X86.Stream.initRd VG.Proof.Rc2.X86.Stream.initWr VG.Proof.Rc2.X86.Stream.wideInit_pre ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Rc2.X86.Stream.initRd, VG.Proof.Rc2.X86.Stream.initWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp only [h, true_or, or_true]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Rc2.X86.Stream.initWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h <;> simp only [h, true_or, or_true]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

theorem update_verified (d : Spec.Rc2.Direction) :
    Verified target (Impl.Rc2.X86.Stream.update d) (Proof.Rc2.cbcUpdateScratchContract abi d 40) := by
  have hsat := (VG.Proof.Rc2.X86.Stream.update_implies d).sat_left
  have narrowSat : ∃ s, (VG.Proof.Rc2.X86.Stream.updateContract d).pre s := by
    obtain ⟨s, hs⟩ := hsat
    exact ⟨_, VG.Proof.Rc2.X86.Stream.wideUpdate_pre d s hs⟩
  apply Verified.of_implies _ (VG.Proof.Rc2.X86.Stream.update_implies d)
  refine Verified.narrowTo
    (Verified.of_correct (fun s hs => Update.update_correct d s hs) (Update.update_constantTime d)
      (.refl narrowSat))
    VG.Proof.Rc2.X86.Stream.updateRd VG.Proof.Rc2.X86.Stream.updateWr (VG.Proof.Rc2.X86.Stream.wideUpdate_pre d) ?_ ?_ ?_ ?_ hsat
  · intro s h
    obtain ⟨rd, wr, _⟩ := h
    rw [rd, wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Rc2.X86.Stream.updateRd, VG.Proof.Rc2.X86.Stream.updateWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    rcases hr with h | h | h | h | h <;> simp only [h, true_or, or_true]
  · intro s h
    obtain ⟨_, wr, _⟩ := h
    rw [wr]
    intro a n ⟨r, hr, hc⟩
    refine ⟨r, ?_, hc⟩
    simp only [VG.Proof.Rc2.X86.Stream.updateWr, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with h | h | h <;> simp only [h, true_or, or_true]
  · intro s s' _ h
    narrow at h ⊢
    exact h
  · intro s₁ s₂ _ _ h
    narrow
    exact h

theorem encryptUpdate_verified :
    Verified target Impl.Rc2.X86.Stream.encryptUpdate (Proof.Rc2.cbcEncryptUpdateScratchContract abi 40) :=
  VG.Proof.Rc2.X86.Stream.update_verified .encrypt

theorem decryptUpdate_verified :
    Verified target Impl.Rc2.X86.Stream.decryptUpdate (Proof.Rc2.cbcDecryptUpdateScratchContract abi 40) :=
  VG.Proof.Rc2.X86.Stream.update_verified .decrypt

end VG.Proof.Rc2.X86.Stream

end

/- Proofs formerly in `VerifiedGarbage.Proof.Rc2.X86.Stream.Frame`. -/
section

/-!
# RC2-CBC's streaming functions on x86, with their working space on the stack

`init` and the updates run their code, proved with the working space as an
argument (`Verified.lean`), in a frame of 608 bytes that allocates it and
copies the six argument slots (`Verified.stackScratchWiped`), and zero it
before returning.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

/-- A state satisfying `vg_rc2_cbc_init`'s precondition, without the working
space. -/
def initFrameSat : State := { VG.Proof.Rc2.X86.Stream.initSat with
                                           wr := [⟨0x3000, 144⟩, ⟨0x6004, 24⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Rc2.cbcInitContract X86.abi 632).pre s := by
  implies_sat [Spec.Rc2.cbcInitContract, Spec.Rc2.cbcInitSig, Spec.Rc2.cbcInitPost, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes]
    [initFrameSat, initSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.Rc2.X86.Stream.initFrameSat

theorem init_framed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 608 6 144 Impl.Rc2.X86.Stream.init)
      (Spec.Rc2.cbcInitContract X86.abi 632) :=
  X86.Verified.stackScratchWiped (sig := Spec.Rc2.cbcInitSig) (nm := "scratch") (e := .u64)
    (n := 72) (post := Spec.Rc2.cbcInitPost X86.abi.ptrBits) (wa := true) (stack := 24)
    (bytes := 608) (words := 144) VG.Proof.Rc2.X86.Stream.init_verified (by decide) (by lit_decide) (by lit_decide)
    (by decide) (fun _ _ _ _ _ _ => by rw [Curry.apply_const]; trivial) (cbcInitPost_local _)
    (cbcInitPostOut_local _) VG.Proof.Rc2.X86.Stream.initFrameSat_pre

/-- A state satisfying the update functions' precondition, without the
working space. -/
def updateFrameSat : State := { VG.Proof.Rc2.X86.Stream.updateSat with
                                               wr := [⟨0x1000, 144⟩, ⟨0x3000, 0⟩, ⟨0x6004, 24⟩] }

theorem updateFrameSat_pre (d : Spec.Rc2.Direction) :
    ∃ s, (Spec.Rc2.cbcUpdateContract X86.abi d 648).pre s := by
  implies_sat [Spec.Rc2.cbcUpdateContract, Spec.Rc2.cbcUpdateSig, Spec.Rc2.cbcUpdatePre,
    Spec.Rc2.cbcUpdatePost, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [updateFrameSat, updateSat, X86.arg, X86.argAddr, Mem.readW, Mem.read] using VG.Proof.Rc2.X86.Stream.updateFrameSat

theorem encryptUpdate_framed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 608 6 144 Impl.Rc2.X86.Stream.encryptUpdate)
      (Spec.Rc2.cbcEncryptUpdateContract X86.abi 648) :=
  X86.Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre X86.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .encrypt X86.abi.ptrBits) (wa := true) (stack := 40)
    (bytes := 608) (words := 144) VG.Proof.Rc2.X86.Stream.encryptUpdate_verified (by decide) (by lit_decide)
    (by lit_decide) (by decide) (cbcUpdatePre_local _) (cbcUpdatePost_local _ _)
    (cbcUpdatePostOut_local _ _) (VG.Proof.Rc2.X86.Stream.updateFrameSat_pre .encrypt)

theorem decryptUpdate_framed :
    Verified X86.target
      (Impl.StackScratch.X86.withStackScratchWiped 608 6 144 Impl.Rc2.X86.Stream.decryptUpdate)
      (Spec.Rc2.cbcDecryptUpdateContract X86.abi 648) :=
  X86.Verified.stackScratchWiped (sig := Spec.Rc2.cbcUpdateSig) (nm := "scratch") (e := .u64)
    (n := 72) (pre := Spec.Rc2.cbcUpdatePre X86.abi.ptrBits)
    (post := Spec.Rc2.cbcUpdatePost .decrypt X86.abi.ptrBits) (wa := true) (stack := 40)
    (bytes := 608) (words := 144) VG.Proof.Rc2.X86.Stream.decryptUpdate_verified (by decide) (by lit_decide)
    (by lit_decide) (by decide) (cbcUpdatePre_local _) (cbcUpdatePost_local _ _)
    (cbcUpdatePostOut_local _ _) (VG.Proof.Rc2.X86.Stream.updateFrameSat_pre .decrypt)

end VG.Proof.Rc2.X86.Stream

end
