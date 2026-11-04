module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Impl.RsaOaep.RISCV64
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Hmac.Stream.RISCV64.Hash
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Mgf1.Bytes

/-!
# RSA paddings on RISC-V: the state in the frame

Untrusted: everything here is checked by Lean. As on PPC64LE
(`Proof/RsaOaep/PPC64LE/Base.lean`, `View.lean`, `Calls.lean`), for any
entry state `s` whose working space starts at `S s` and whose values of
`s1`–`s4` are `vf s`: our part of the working space, `SC S s` (its first
`oRsa` bytes), seen as a function from offsets to bytes (`view`); and
`Base S vf s t`: the state `t` is in the frame with our caller's registers
and return address in their slots (`Saves`), `s0` holds `S s` and `s1`–`s4`
their values, and memory is changed only in the stack the function uses and
in `SC S s`. Code that writes other registers, ranges of `SC S s` and the
208 bytes below the frame keeps it (`Base.keep`, `Base.only`, `Base.wb`),
given what the code needs of the entry state (`Fits`); the caller's buffers
are then as on entry (`bytes_entry`, `words_entry`). The calls of a hash
function's `init`, `update` and `finalize` on the streaming state at
`S + oSt`, the digest to `S + oDig` (`init_ok`, `upd_ok`, `fin_ok`), keep
`Base`, the callee-saved registers, and the bytes of our part of the working
space outside the ranges they write (`Same`).
-/

@[expose] public section

/-!
# RSAES-OAEP encryption on RISC-V: the frame

Untrusted: everything here is checked by Lean. The frame of
`vg_rsa_oaep_<H>_mgf1_encrypt_precomputed` (`Impl/RsaOaep/RISCV64.lean`),
from its base `fb`, which its allocation makes writable (`fr`), and the 208
bytes below it that the streaming hash functions use (`cR`): the stack the
function uses, `kR`, the 336 bytes below the stack pointer on entry. As on
PPC64LE (`Proof/RsaOaep/PPC64LE/Frame.lean`): `save_ok`, the saves of
`s0`–`s11` and of the return address; `Saves`, what the restores need, kept
by code writing other registers and memory apart from the slots;
`restore_ok`, the restores giving back the caller's registers.
-/


namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo wp_addSp)

/-! ## Addresses -/

/-- The bytes of stack the function uses: the frame and the 208 bytes below
it. -/
def stackBytes : Nat := 336

/-- The frame's base: the stack pointer in the frame. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses. -/
abbrev kR (s : State) : Region := below s.sp stackBytes

/-- The frame, which its allocation makes writable. -/
abbrev fr (s : State) : Region := ⟨fb s, frameBytes⟩

/-- The 208 bytes below the frame, which the streaming hash functions use. -/
abbrev cR (s : State) : Region := below (fb s) 208

/-- An address of the frame, from the base of `kR`. -/
theorem fb_off (s : State) (d : Nat) :
    fb s + BitVec.ofNat 64 d = (s.sp - BitVec.ofNat 64 stackBytes) + BitVec.ofNat 64 (208 + d) := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_comm,
    show (stackBytes : Nat) = frameBytes + 208 from rfl]
  bv_omega

theorem cR_eq (s : State) : cR s = ⟨s.sp - BitVec.ofNat 64 stackBytes, 208⟩ := by
  simp only [cR, below, Region.mk.injEq, and_true]
  rw [BitVec.sub_sub]; rfl

/-- A region of the frame is in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (kR s) := by
  rw [fb_off]; exact Offset.sub_base _ (by simp only [frameBytes, stackBytes] at *; omega)

theorem frame_contains (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (kR s).Contains (fb s + BitVec.ofNat 64 d) n := by
  rw [fb_off]
  exact Offset.contains_base _ (by simp only [frameBytes, stackBytes] at *; omega)
    (by simp only [frameBytes] at h; omega)

theorem fr_sub (s : State) : Region.Sub (fr s) (kR s) := by
  have := frame_sub s (d := 0) (n := frameBytes) (by omega); rwa [BitVec.add_zero] at this

theorem cR_sub (s : State) : Region.Sub (cR s) (kR s) := by
  have := Offset.sub_base (s.sp - BitVec.ofNat 64 stackBytes) (d := 0) (n := 208) (k := stackBytes)
    (by unfold stackBytes; omega)
  rw [BitVec.add_zero] at this; rw [cR_eq]; exact this

/-- The frame is writable. -/
theorem in_fr (s : State) (rs : List Region) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (fr s :: rs) (fb s + BitVec.ofNat 64 d) n :=
  ⟨_, List.mem_cons_self .., Offset.contains_base _ h (by unfold frameBytes at h; omega)⟩

theorem in_fr' (s : State) (rd rs : List Region) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (rd ++ fr s :: rs) (fb s + BitVec.ofNat 64 d) n := by
  obtain ⟨r, hr, hc⟩ := in_fr s rs h
  exact ⟨r, List.mem_append_right _ hr, hc⟩

/-- Our stack arguments, from the frame. -/
theorem stackArgAddr_fb (s : State) (j : Nat) :
    stackArgAddr s j = fb s + BitVec.ofNat 64 (frameBytes + 8 * j) := by
  rw [stackArgAddr, ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc, BitVec.sub_add_cancel]

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

/-! ## The saves -/

theorem save_eq : save = ([.addSp .t0 0] : List Instr) ++ Spill.saveCode .t0 saved := rfl

theorem restore_eq : restore = ([.addSp .t0 0] : List Instr) ++ Spill.restoreCode .t0 saved := rfl

/-- Where the slots are. -/
def oSv : Nat := 16

theorem saved_offs : ∀ p ∈ saved, oSv ≤ p.2 ∧ p.2 + 8 ≤ frameBytes := by decide

theorem saved_ho : ∀ p ∈ saved, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem preserved_saved {r : Reg} (h : r ∈ preserved) : r ∈ saved.map Prod.fst := by
  revert r; decide

/-- The saves, from the state after the allocation (`u`): `t0` holds the
frame's base, `s0`–`s11` and the return address are in their slots, and
memory is changed only in the frame. -/
theorem save_ok {s u : State} (hsp : u.sp = fb s) (hwr : u.wr = fr s :: s.wr) (hal : (fb s).toNat % 8 = 0)
    (hm : Frame [kR s] s.mem u.mem) (hg : ∀ r ∈ preserved ++ ([.ra] : List Reg), u.gpr r = s.gpr r)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ v, Kept [.t0] u v → v.gpr .t0 = fb s → Frame [kR s] s.mem v.mem →
      Spill.Saved (fb s) s.gpr saved v.mem → WP isa (.block rest) v Q) :
    WP isa (.block (save ++ rest)) u Q := by
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun u₁ o₁ e₁ => ?_
  rw [hsp, BitVec.add_zero] at e₁
  refine Spill.save_ok (b := .t0) (l := saved) (by rw [e₁]; exact hal) saved_ho (fun p hp => ?_) ?_
  · have := saved_offs p hp
    rw [e₁, o₁.wr, hwr]; exact in_fr s _ this.2
  refine k _ ⟨fun r hr => o₁.gpr r hr, o₁.rd, o₁.wr, o₁.sp⟩ e₁ ?_ ?_
  · show Frame [kR s] s.mem (Spill.saveMem u₁.mem (u₁.gpr .t0) u₁.gpr saved)
    rw [e₁, o₁.mem]
    exact hm.trans ((Spill.saveMem_frame_base (fun p hp => (saved_offs p hp).2) (by decide) _ _ _).sub
      fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, fr_sub s⟩)
  · show Spill.Saved (fb s) s.gpr saved (Spill.saveMem u₁.mem (u₁.gpr .t0) u₁.gpr saved)
    rw [e₁]
    refine fun p hp => (Spill.saveMem_saved (by decide) _ _ _ p hp).trans ?_
    have h0 : p.1 ∉ [Reg.t0] := by revert p; decide
    rw [o₁.gpr _ h0, hg _ (by revert p; decide)]

/-- What the restores need: the frame and our caller's registers and return
address in their slots. -/
structure Saves (s t : State) : Prop where
  sp : t.sp = fb s
  wr : t.wr = fr s :: s.wr
  sv : Spill.Saved (fb s) s.gpr saved t.mem

/-- The slots. -/
abbrev slR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oSv, frameBytes - oSv⟩

theorem slR_sub (s : State) : Region.Sub (slR s) (kR s) := frame_sub s (by decide)

theorem slot_sub {p : Reg × Nat} (hp : p ∈ saved) (s : State) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 p.2, 8⟩ (slR s) := by
  have := saved_offs p hp
  exact Offset.sub _ (n := 8) this.1 (by unfold frameBytes oSv at *; omega)

/-- `Saves` is kept by code keeping the stack pointer and the regions, and
writing memory apart from the slots. -/
theorem Saves.keep {s t w : State} {rs : List Reg} (h : Saves s t) (o : Kept rs t w) {R : List Region}
    (hm : Frame R t.mem w.mem) (hR : ∀ r ∈ R, (slR s).Disjoint r) : Saves s w where
  sp := o.sp.trans h.sp
  wr := o.wr.trans h.wr
  sv := h.sv.frame hm fun _ hp r hr => (hR r hr).sub_left (slot_sub hp s)

/-- The restores: the caller's registers and return address are back, and
`a0` and memory are kept. -/
theorem restore_ok {s w : State} (hm : Saves s w) (hal : (fb s).toNat % 8 = 0) :
    WP isa (.block restore) w fun w' =>
      abiPreserved s (freed frameBytes w') ∧ w'.gpr .a0 = w.gpr .a0 ∧ w'.mem = w.mem := by
  rw [restore_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp fun w₁ o₁ e₁ => ?_
  rw [hm.sp, BitVec.add_zero] at e₁
  refine WP.mono (Spill.restore_wp (b := .t0) (l := saved) (B := fb s) (g := s.gpr) hal
    e₁ saved_ho (by decide)
    (fun p hp => by
      rw [o₁.rd, o₁.wr, hm.wr]; exact in_fr' s _ _ (saved_offs p hp).2)
    (by rw [o₁.mem]; exact hm.sv)) fun w' hr => ⟨⟨fun r hr' => ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact hr.gpr_of (.inl (preserved_saved hr'))
  · show w'.sp + BitVec.ofNat 64 frameBytes = s.sp
    rw [hr.sp, o₁.sp, hm.sp, BitVec.sub_add_cancel]
  · show w'.gpr .ra = s.gpr .ra
    exact hr.gpr_of (.inl (by simp [saved]))
  · show w'.gpr .a0 = w.gpr .a0
    rw [hr.other .a0 (by decide), o₁.get .a0]
  · rw [hr.mem, o₁.mem]

end VG.Proof.RsaOaep.RISCV64


namespace VG.Proof.RsaOaep.RISCV64

open VG VG.RISCV64 VG.Impl.RsaOaep.RISCV64 VG.WriteBytes
open VG.Proof.RsaPkcs1Sig.RISCV64 (Only Kept MemTo)
open VG.Impl.Hmac.Stream.RISCV64 (Hash)
open VG.Proof.Hmac.Stream.RISCV64 (HashOK)
open VG.Proof.Mgf1 (ifp ifn)

/-- `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

theorem off_off (p : Addr) (a b : Nat) : off (off p a) b = off p (a + b) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

/-- Our part of the working space at `S s`. -/
abbrev SC (S : State → Addr) (s : State) : Region := ⟨S s, oRsa⟩

/-- Memory at `S`, as a function from offsets to bytes. -/
def view (m : Mem) (S : Addr) (o : Nat) : Byte := m (off S o)

/-- What the shared code needs of the entry state `s`, whose working space is
at `S s`: room for the frame and the calls below it, an aligned stack
pointer, our part of the working space writable and apart from that stack,
and not wrapping around. -/
structure Fits (S : State → Addr) (s : State) : Prop where
  sp1 : stackBytes ≤ s.sp.toNat
  sp16 : s.sp.toNat % 16 = 0
  sc : ∃ R ∈ s.wr, R.base = S s ∧ oRsa ≤ R.len
  ksc : (kR s).Disjoint (SC S s)
  wS : (S s).toNat + oRsa ≤ 2 ^ 64

section
variable {S : State → Addr} {s : State} (P : Fits S s)
include P

omit P in
/-- A range of our part of the working space is in it. -/
theorem sc_in {o n : Nat} (h : o + n ≤ oRsa) : Region.Sub ⟨off (S s) o, n⟩ (SC S s) :=
  Offset.sub_base _ h

/-- A range of our part of the working space is writable. -/
theorem sc_cov {o n : Nat} (h : o + n ≤ oRsa) : Covers [⟨off (S s) o, n⟩] (fr s :: s.wr) :=
  Covers.of_sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    obtain ⟨R, hR, hb, hl⟩ := P.sc
    exact ⟨R, List.mem_cons_of_mem _ hR, o, by rw [hb], by simp only; omega⟩

theorem sc_inR {o n : Nat} (h : o + n ≤ oRsa) (rd : List Region) :
    InRegions (rd ++ (fr s :: s.wr)) (off (S s) o) n :=
  Covers.right (sc_cov P h) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem sc_inW {o n : Nat} (h : o + n ≤ oRsa) : InRegions (fr s :: s.wr) (off (S s) o) n :=
  sc_cov P h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

/-- Our part of the working space and the stack the function uses are apart. -/
theorem slR_sc : (slR s).Disjoint (SC S s) := P.ksc.sub_left (slR_sub s)

theorem cR_sc : (cR s).Disjoint (SC S s) := P.ksc.sub_left (cR_sub s)

omit P in
/-- Two ranges of our part of the working space that do not overlap. -/
theorem sdis {a n b k : Nat} (h : a + n ≤ b ∨ b + k ≤ a) (ha : a + n ≤ oRsa) (hb : b + k ≤ oRsa) :
    Region.Disjoint ⟨off (S s) a, n⟩ ⟨off (S s) b, k⟩ :=
  Offset.disjoint _ h (by unfold oRsa at ha; omega) (by unfold oRsa at hb; omega)

/-- The 208 bytes below the frame and a range of our part of the working
space. -/
theorem cR_dis {o n : Nat} (h : o + n ≤ oRsa) : (cR s).Disjoint ⟨off (S s) o, n⟩ :=
  (cR_sc P).sub_right (sc_in h)

theorem fb_al : (fb s).toNat % 16 = 0 := by
  have := P.sp1; have := P.sp16
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes, stackBytes] at *; omega

theorem fb_ge : 208 ≤ (fb s).toNat := by
  have := P.sp1
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat, frameBytes, stackBytes] at *; omega

end

theorem cR_slR (s : State) : (cR s).Disjoint (slR s) := by
  rw [cR_eq]
  have e : slR s = ⟨(s.sp - BitVec.ofNat 64 stackBytes) + BitVec.ofNat 64 (208 + oSv), frameBytes - oSv⟩ := by
    simp only [slR]; rw [fb_off]
  rw [e]
  have := Offset.disjoint (s.sp - BitVec.ofNat 64 stackBytes) (d := 0) (n := 208) (e := 208 + oSv)
    (k := frameBytes - oSv) (.inl (by omega)) (by omega) (by decide)
  rwa [BitVec.add_zero] at this

/-! ## The state in the frame -/

/-- The registers `Base` fixes but `s0`. -/
def fx : List Reg := [.s1, .s2, .s3, .s4]

structure Base (S : State → Addr) (vf : State → Reg → BitVec 64) (s t : State) : Prop where
  sv : Saves s t
  rd : t.rd = s.rd
  s0 : t.gpr .s0 = S s
  vs : ∀ r ∈ fx, t.gpr r = vf s r
  mem : Frame [kR s, SC S s] s.mem t.mem

/-- A region written by code that keeps `Base`: in our part of the working
space, or the 208 bytes below the frame. -/
def Ours (S : State → Addr) (s : State) (r : Region) : Prop := Region.Sub r (SC S s) ∨ r = cR s

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s t w : State} {rs : List Reg}

theorem Base.sp (h : Base S vf s t) : t.sp = fb s := h.sv.sp
theorem Base.wr (h : Base S vf s t) : t.wr = fr s :: s.wr := h.sv.wr

/-- `Base` is kept by code that keeps the stack pointer, the regions and the
registers it fixes, and writes memory only in our ranges. -/
theorem Base.of (P : Fits S s) (h : Base S vf s t) (hsp : w.sp = t.sp) (hrd : w.rd = t.rd) (hwr : w.wr = t.wr)
    (hg : ∀ r ∈ .s0 :: fx, w.gpr r = t.gpr r) {R : List Region} (hm : Frame R t.mem w.mem)
    (hR : ∀ r ∈ R, Ours S s r) : Base S vf s w where
  sv := by
    have hd : ∀ r ∈ R, (slR s).Disjoint r := fun r hr => by
      rcases hR r hr with h' | rfl
      · exact (slR_sc P).sub_right h'
      · exact (cR_slR s).symm
    exact ⟨hsp.trans h.sv.sp, hwr.trans h.sv.wr,
      h.sv.sv.frame hm fun _ hp r hr => (hd r hr).sub_left (slot_sub hp s)⟩
  rd := hrd.trans h.rd
  s0 := (hg _ (by decide)).trans h.s0
  vs := fun r hr => (hg r (List.mem_cons_of_mem _ hr)).trans (h.vs r hr)
  mem := h.mem.trans (hm.sub fun r hr => by
    rcases hR r hr with h' | rfl
    · exact ⟨SC S s, by simp, h'⟩
    · exact ⟨kR s, by simp, cR_sub s⟩)


/-- The registers `Base` fixes. -/
def fixed : List Reg := .s0 :: fx

/-- `Base` is kept by code writing registers other than those it fixes, and
memory in our ranges. -/
theorem Base.keep (P : Fits S s) (h : Base S vf s t) (o : Kept rs t w) {R : List Region}
    (hm : Frame R t.mem w.mem) (hR : ∀ r ∈ R, Ours S s r) (hrs : ∀ r ∈ rs, r ∉ fixed := by decide) :
    Base S vf s w :=
  h.of P o.sp o.rd o.wr (fun r hr => o.gpr r fun h' => hrs r h' hr) hm hR

/-- `Base` is kept by code writing registers other than those it fixes. -/
theorem Base.only (P : Fits S s) (h : Base S vf s t) (o : Only rs t w)
    (hrs : ∀ r ∈ rs, r ∉ fixed := by decide) : Base S vf s w :=
  h.keep P o.keep (R := []) (by rw [o.mem]; exact Frame.refl _ _) (by simp) hrs

/-- A call keeps `Base` if it writes only our ranges and the 208 bytes below
the stack pointer, and keeps the callee-saved registers. -/
theorem Base.call (P : Fits S s) (h : Base S vf s t) {R : List Region} (hR : ∀ r ∈ R, Region.Sub r (SC S s))
    (hrd : w.rd = t.rd) (hwr : w.wr = t.wr) (hsp : w.sp = t.sp) (hm : Frame (R ++ [below t.sp 208]) t.mem w.mem)
    (hg : ∀ r ∈ preserved, w.gpr r = t.gpr r) : Base S vf s w :=
  h.of P hsp hrd hwr (fun r hr => hg r (by revert r; decide)) hm fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact .inl (hR r hr)
    · rw [List.mem_singleton.mp hr, h.sp]; exact .inr rfl

end

/-! ## The caller's buffers -/

/-- A buffer that the function does not write. -/
theorem bytes_entry {A B : Region} {m m' : Mem} (hf : Frame [A, B] m m') {p : Addr} {len : Nat}
    (ha : A.Disjoint ⟨p, len⟩) (hb : B.Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' p len = Spec.Rsa.bytesAt m p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ha.symm
  · exact hb.symm

theorem words_entry {A B : Region} {m m' : Mem} (hf : Frame [A, B] m m') {p : Addr} {n : Nat}
    (ha : A.Disjoint ⟨p, n * 8⟩) (hb : B.Disjoint ⟨p, n * 8⟩) (hl : p.toNat + n * 8 ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m' p n = Spec.Rsa.wordsAt m p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => hf.readW (r := ⟨p, n * 8⟩) ?_ (fun r hr => ?_) (by decide)
  · have := List.mem_range.mp hi
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ha.symm
    · exact hb.symm

/-! ## Views of writes -/

theorem view_wb (m : Mem) {S : Addr} {d o : Nat} (xs : List Byte)
    (hd : d + xs.length ≤ oRsa) (ho : o < oRsa) :
    view (writeBytes m (off S d) xs) S o = if d ≤ o ∧ o < d + xs.length then xs.getD (o - d) 0 else view m S o := by
  simp only [view, writeBytes]
  rw [Offset.sub_toNat' S (by unfold oRsa at *; omega) (by unfold oRsa at *; omega)]
  by_cases h : d ≤ o
  · rw [ifp h]
    by_cases h' : o - d < xs.length
    · rw [ifp h', ifp ⟨h, by omega⟩]
    · rw [ifn h', ifn (by omega)]
  · rw [ifn h, ifn (by unfold oRsa at *; omega), ifn (by omega)]

theorem view_w8 (m : Mem) {S : Addr} {d o : Nat} (b : Byte) (hd : d < oRsa)
    (ho : o < oRsa) : view (m.writeW (off S d) b) S o = if o = d then b else view m S o := by
  simp only [view]
  rw [writeW8_apply]
  by_cases h : o = d
  · subst h; simp
  · rw [ifn (Offset.add_ofNat_ne S (by unfold oRsa at *; omega) (by unfold oRsa at *; omega) h), ifn h]

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (P : Fits S s)
include P

/-- The bytes at `S + d`, `d + n ≤ oRsa`, are writable. -/
theorem sc_w {t : State} (ht : t.wr = fr s :: s.wr) {d n : Nat} (hd : d + n ≤ oRsa) :
    ∀ i < n, InRegions t.wr (off (S s) d + BitVec.ofNat 64 i) 1 := fun i hi => by
  show InRegions t.wr (off (off (S s) d) i) 1
  rw [ht, off_off]; exact sc_inW P (by omega)

omit P in
/-- Bytes of a caller's buffer are readable. -/
theorem rd_in {t : State} (ht : t.rd = s.rd) {R : Region} (hR : R ∈ s.rd) (hw : R.base.toNat + R.len ≤ 2 ^ 64)
    {n : Nat} (hn : n ≤ R.len) : ∀ j < n, InRegions (t.rd ++ t.wr) (R.base + BitVec.ofNat 64 j) 1 := fun j hj => by
  rw [ht]
  exact ⟨R, List.mem_append_left _ hR, Offset.contains_base _ (by omega) (by omega)⟩

omit P in
/-- Bytes of two disjoint regions are at different addresses. -/
theorem ne_of_dis {A B : Region} (h : A.Disjoint B) {a b : Addr} (ha : A.Contains a 1) (hb : B.Contains b 1) :
    a ≠ b := fun e => h a ha (e ▸ hb)

/-- A write of bytes to our part of the working space keeps `Base`. -/
theorem Base.wb {t w : State} {rs : List Reg} (h : Base S vf s t) (o : Kept rs t w) {d : Nat} {xs : List Byte}
    (hd : d + xs.length ≤ oRsa) (hm : w.mem = writeBytes t.mem (off (S s) d) xs)
    (hrs : ∀ r ∈ rs, r ∉ fixed := by decide) : Base S vf s w :=
  h.keep P o (R := [⟨off (S s) d, xs.length⟩]) (by rw [hm]; exact writeBytes_frame _ _ _ (Region.contains_self _ _))
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact .inl (sc_in hd)) hrs

end

/-! ## The calls of the streaming hash functions -/

/-- Our part of the working space is as in `t` outside the ranges `rgs`. -/
def Same (S : Addr) (t t' : State) (rgs : List (Nat × Nat)) : Prop :=
  ∀ o < oRsa, (∀ p ∈ rgs, o < p.1 ∨ p.1 + p.2 ≤ o) → view t'.mem S o = view t.mem S o

theorem Same.refl (S : Addr) (t : State) (rgs : List (Nat × Nat)) : Same S t t rgs := fun _ _ _ => rfl

theorem Same.trans {S : Addr} {t₁ t₂ t₃ : State} {rgs : List (Nat × Nat)} (h₁ : Same S t₁ t₂ rgs)
    (h₂ : Same S t₂ t₃ rgs) : Same S t₁ t₃ rgs := fun o ho hr => (h₂ o ho hr).trans (h₁ o ho hr)

theorem Same.mono {S : Addr} {t t' : State} {rgs rgs' : List (Nat × Nat)} (h : Same S t t' rgs)
    (hs : ∀ p ∈ rgs, p ∈ rgs') : Same S t t' rgs' := fun o ho hr => h o ho fun p hp => hr p (hs p hp)

theorem Same.of_mem {S : Addr} {t t' : State} (h : t'.mem = t.mem) (rgs : List (Nat × Nat)) : Same S t t' rgs :=
  fun _ _ _ => by simp only [view, h]

/-- The offsets in our part of the working space. -/
theorem offs : oEm = 0 ∧ oSt = 1024 ∧ oDig = 1280 ∧ oCtr = 1344 ∧ oRsa = 8192 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The sizes of a hash function's ranges in our part of the working space. -/
theorem hfits {H : Hash} (hH : HashOK H) : H.S ≤ 192 ∧ H.D ≤ 64 := by
  have := hH.hN.2; have := hH.hD64
  rcases hH.hB64 with h | h <;> simp only [Hash.S, h] <;> omega

section
variable {S : State → Addr} {vf : State → Reg → BitVec 64} {s : State} (P : Fits S s)
include P

/-- What a callee writing ranges of our part of the working space and the
208 bytes below the frame keeps of it. -/
theorem same_of_frame {t t' : State} (hsp : t.sp = fb s) {rgs : List (Nat × Nat)}
    (hrg : ∀ p ∈ rgs, p.1 + p.2 ≤ oRsa)
    (hf : Frame (rgs.map (fun p => (⟨off (S s) p.1, p.2⟩ : Region)) ++ [below t.sp 208]) t.mem t'.mem) :
    Same (S s) t t' rgs := fun o ho hr => by
  simp only [view]
  refine hf _ fun r hr' hc => ?_
  rcases List.mem_append.mp hr' with h' | h'
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h'
    have := hrg p hp
    rcases hr p hp with h₁ | h₁
    · exact sdis (s := s) (a := o) (n := 1) (b := p.1) (k := p.2) (.inl (by omega)) (by omega) (by omega) _
        (Region.contains_self _ _) hc
    · exact sdis (s := s) (a := o) (n := 1) (b := p.1) (k := p.2) (.inr (by omega)) (by omega) (by omega) _
        (Region.contains_self _ _) hc
  · rw [List.mem_singleton.mp h', hsp] at hc
    exact cR_dis P (o := o) (n := 1) (by omega) _ hc (Region.contains_self _ _)

theorem Base.al {t : State} (h : Base S vf s t) : t.sp.toNat % 16 = 0 := by rw [h.sp]; exact fb_al P

theorem Base.spF {t : State} (h : Base S vf s t) {F : Nat} (hF : F ≤ 208) : F ≤ t.sp.toNat := by
  rw [h.sp]; have := fb_ge P; omega

theorem Base.cRd {t : State} (h : Base S vf s t) {F : Nat} (hF : F ≤ 208) {o n : Nat} (ho : o + n ≤ oRsa) :
    (below t.sp F).Disjoint ⟨off (S s) o, n⟩ := by
  rw [h.sp]
  exact (cR_dis P ho).sub_left (below_sub hF (by omega))

omit P in
theorem frame208 {F : Nat} (hF : F ≤ 208) {wr : List Region} {sp : Addr} {m m' : Mem}
    (h : Frame (wr ++ [below sp F]) m m') : Frame (wr ++ [below sp 208]) m m' :=
  Frame.below_mono h hF (by omega)

/-- A call of the streaming `init` on the state at `S + oSt`. -/
theorem init_ok {H : Hash} (hH : HashOK H) (hF : H.F ≤ 208) {t : State} (h : Base S vf s t)
    (h0 : t.gpr .a0 = off (S s) oSt) :
    WP isa H.callInit t fun t' => Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S)] ∧ hH.SH.Repr t'.mem (off (S s) oSt) [] := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  have hc : Covers [⟨off (S s) oSt, H.S⟩] t.wr := by rw [h.wr]; exact sc_cov P (by omega)
  refine hH.callInit_ok h0 (Covers.right hc) hc fun t' hrd hwr hsp hf hg hr => ?_
  have hf' := frame208 hF hf
  exact ⟨h.call P (R := [⟨off (S s) oSt, H.S⟩]) (fun r hr' => by
      rw [List.mem_singleton.mp hr']; exact sc_in (by omega)) hrd hwr hsp hf' hg, hg,
    same_of_frame P h.sp (rgs := [(oSt, H.S)]) (by simp; omega) hf', hr⟩

/-- A call of the streaming `update` on the state at `S + oSt`, with the
`len` bytes at `dat`. -/
theorem upd_ok {H : Hash} (hH : HashOK H) (hF : H.F ≤ 208) {t : State} (h : Base S vf s t) {dat : Addr}
    {len : Nat} (h0 : t.gpr .a0 = off (S s) oSt) (h2 : t.gpr .a2 = dat) (h3 : (t.gpr .a3).toNat = len)
    (hdc : Covers [⟨dat, len⟩] (t.rd ++ t.wr))
    (hd₁ : Region.Disjoint ⟨dat, len⟩ ⟨off (S s) oSt, H.S⟩) (hd₃ : (cR s).Disjoint ⟨dat, len⟩) :
    WP isa H.callUpd t fun t' => Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S)] ∧
      ∀ m, hH.SH.Repr t.mem (off (S s) oSt) m → t.gpr .a1 = BitVec.ofNat 64 m.length →
        hH.SH.Repr t'.mem (off (S s) oSt) (m ++ Spec.Sha256.bytesAt t.mem dat len) := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  have hc : Covers [⟨off (S s) oSt, H.S⟩] t.wr := by rw [h.wr]; exact sc_cov P (by omega)
  refine hH.callUpd_ok h0 h2 h3 hd₁ (h.al P) (h.spF P hF) (h.cRd P hF (by omega))
    (by rw [h.sp]; exact hd₃.sub_left (below_sub hF (by omega)))
    (Covers.append_left hdc (Covers.right hc)) hc fun t' hrd hwr hsp hf hg hr => ?_
  have hf' := frame208 hF hf
  exact ⟨h.call P (R := [⟨off (S s) oSt, H.S⟩]) (fun r hr' => by
      rw [List.mem_singleton.mp hr']; exact sc_in (by omega)) hrd hwr hsp hf' hg, hg,
    same_of_frame P h.sp (rgs := [(oSt, H.S)]) (by simp; omega) hf', hr⟩

/-- A call of the streaming `finalize` on the state at `S + oSt`, its digest
to `S + oDig`. -/
theorem fin_ok {H : Hash} (hH : HashOK H) (hF : H.F ≤ 208) {t : State} (h : Base S vf s t)
    (h0 : t.gpr .a0 = off (S s) oSt) (h2 : t.gpr .a2 = off (S s) oDig) :
    WP isa H.callFin t fun t' => Base S vf s t' ∧ (∀ r ∈ preserved, t'.gpr r = t.gpr r) ∧
      Same (S s) t t' [(oSt, H.S), (oDig, H.D)] ∧
      ∀ m, hH.SH.Repr t.mem (off (S s) oSt) m → m.length < 2 ^ 64 → t.gpr .a1 = BitVec.ofNat 64 m.length →
        Spec.Sha256.bytesAt t'.mem (off (S s) oDig) H.D = hH.SH.H.hash m := by
  have F := hfits hH
  obtain ⟨_, _, _, _, _⟩ := offs
  have hc : Covers [⟨off (S s) oSt, H.S⟩, ⟨off (S s) oDig, H.D⟩] t.wr := by
    rw [h.wr]; exact Covers.pair (sc_cov P (by omega)) (sc_cov P (by omega))
  refine hH.callFin_ok h0 h2 (sdis (.inl (by omega)) (by omega) (by omega)) (h.al P) (h.spF P hF)
    (h.cRd P hF (by omega)) (h.cRd P hF (by omega)) (Covers.right hc) hc
    fun t' hrd hwr hsp hf hg hr => ?_
  have hf' := frame208 hF hf
  exact ⟨h.call P (R := [⟨off (S s) oSt, H.S⟩, ⟨off (S s) oDig, H.D⟩]) (fun r hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact sc_in (by omega)
      · exact sc_in (by omega)) hrd hwr hsp hf' hg, hg,
    same_of_frame P h.sp (rgs := [(oSt, H.S), (oDig, H.D)]) (by simp; omega) hf', hr⟩

end

end VG.Proof.RsaOaep.RISCV64
