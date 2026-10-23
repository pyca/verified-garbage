module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Call
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# AES-GCM on PPC64LE: where everything is

Untrusted: everything here is checked by Lean. The pieces of the functions
(`absorb`, `crypt`, …) run with the working space `W` in `r14`, the
streaming state `St` (80 bytes) in `r15` and the key context `C` (256
bytes) in `r16` (`Env`): `W` and `St` writable, `C` readable, the three
apart and not wrapping around. They write only `St` and the first 2112 bytes
of `W` (`[0, 2048)` for the functions called, then the blocks of
`Impl/AesGcm/PPC64LE.lean`), below the saved registers, and keep the
permissions, the stack pointer and every nonvolatile register but `r18`,
`r19` and `r20` (`PK`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.PPC64LE

open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Proof.Gather.PPC64LE (Keeps)

/-! ## What the pieces keep -/

/-- The nonvolatile registers the pieces keep. -/
def keepRegs : List Reg :=
  [.r2, .r14, .r15, .r16, .r17, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- What a piece keeps. -/
structure PK (s s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  gpr : ∀ r ∈ keepRegs, s'.gpr r = s.gpr r

theorem PK.refl (s : State) : PK s s := ⟨rfl, rfl, rfl, fun _ _ => rfl⟩

theorem PK.trans {s t u : State} (h₁ : PK s t) (h₂ : PK t u) : PK s u :=
  ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.sp.trans h₁.sp,
    fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr)⟩

theorem PK.ofUpd {s t : State} {d : Reg} {v : BitVec 64} (u : Proof.ChaCha20Poly1305.PPC64LE.Upd s t d v) (hd : d ∉ keepRegs := by decide) :
    PK s t :=
  ⟨u.rd, u.wr, u.sp, fun r hr => u.other r fun h => hd (h ▸ hr)⟩

theorem PK.ofMupd {s t : State} {m : Mem} (u : Proof.ChaCha20Poly1305.PPC64LE.Mupd s t m) : PK s t :=
  ⟨u.rd, u.wr, u.sp, fun r _ => by rw [u.gpr]⟩

theorem keep_copy : ∀ r ∈ keepRegs, r ∉ VG.Proof.Gather.PPC64LE.copyRegs := by decide

theorem PK.ofKeeps {s t : State} (h : Keeps s t) : PK s t :=
  ⟨h.rd, h.wr, h.sp, fun r hr => h.gpr r (keep_copy r hr)⟩

theorem keep_preserved : ∀ r ∈ keepRegs, r ∈ preserved := by decide

theorem PK.ofCall {s t : State} {ws : List Region} (h : CallKeep s t ws) : PK s t :=
  ⟨h.rd, h.wr, h.sp, fun r hr => h.saved r (keep_preserved r hr)⟩

/-! ## The environment -/

/-- The working space's first 2112 bytes, which the pieces may write. -/
abbrev wR (W : Addr) : Region := ⟨W, 2112⟩
abbrev stR (St : Addr) : Region := ⟨St, 80⟩
abbrev cR (C : Addr) : Region := ⟨C, 256⟩

/-- Where the pieces run. -/
structure Env (s : State) (W St C : Addr) : Prop where
  r14 : s.gpr .r14 = W
  r15 : s.gpr .r15 = St
  r16 : s.gpr .r16 = C
  wW : Covers [⟨W, 2560⟩] s.wr
  wSt : Covers [stR St] s.wr
  rC : Covers [cR C] (s.rd ++ s.wr)
  cw : (cR C).Disjoint ⟨W, 2560⟩
  cs : (cR C).Disjoint (stR St)
  sw : (stR St).Disjoint ⟨W, 2560⟩
  wfit : W.toNat + 2560 ≤ 2 ^ 64
  sfit : St.toNat + 80 ≤ 2 ^ 64
  cfit : C.toNat + 256 ≤ 2 ^ 64

/-- The environment is that of any state the pieces lead to. -/
theorem Env.of_pk {s t : State} {W St C : Addr} (h : Env s W St C) (k : PK s t) : Env t W St C where
  r14 := by rw [k.gpr .r14 (by decide), h.r14]
  r15 := by rw [k.gpr .r15 (by decide), h.r15]
  r16 := by rw [k.gpr .r16 (by decide), h.r16]
  wW := by rw [k.wr]; exact h.wW
  wSt := by rw [k.wr]; exact h.wSt
  rC := by rw [k.rd, k.wr]; exact h.rC
  cw := h.cw
  cs := h.cs
  sw := h.sw
  wfit := h.wfit
  sfit := h.sfit
  cfit := h.cfit

section
variable {s : State} {W St C : Addr} (h : Env s W St C)
include h

/-! ### Sub-regions -/

theorem Env.wIn {d n : Nat} (hd : d + n ≤ 2560) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] s.wr :=
  VG.Proof.Gather.PPC64LE.covers_off h.wW hd (by decide)

theorem Env.stIn {d n : Nat} (hd : d + n ≤ 80) : Covers [⟨St + BitVec.ofNat 64 d, n⟩] s.wr :=
  VG.Proof.Gather.PPC64LE.covers_off h.wSt hd (by decide)

theorem Env.cIn {d n : Nat} (hd : d + n ≤ 256) : Covers [⟨C + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  VG.Proof.Gather.PPC64LE.covers_off h.rC hd (by decide)

theorem Env.wInR {d n : Nat} (hd : d + n ≤ 2560) : InRegions s.wr (W + BitVec.ofNat 64 d) n :=
  h.wIn hd _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem Env.stInR {d n : Nat} (hd : d + n ≤ 80) : InRegions s.wr (St + BitVec.ofNat 64 d) n :=
  h.stIn hd _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem Env.wRd {d n : Nat} (hd : d + n ≤ 2560) : Covers [⟨W + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  VG.Covers.right (h.wIn hd)

theorem Env.stRd {d n : Nat} (hd : d + n ≤ 80) : Covers [⟨St + BitVec.ofNat 64 d, n⟩] (s.rd ++ s.wr) :=
  VG.Covers.right (h.stIn hd)

/-! ### Apart -/

theorem Env.st_w {d n e k : Nat} (hd : d + n ≤ 80) (he : e + k ≤ 2560) :
    (⟨St + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ :=
  (h.sw.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ he)

theorem Env.c_w {d n e k : Nat} (hd : d + n ≤ 256) (he : e + k ≤ 2560) :
    (⟨C + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ :=
  (h.cw.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ he)

theorem Env.c_st {d n e k : Nat} (hd : d + n ≤ 256) (he : e + k ≤ 80) :
    (⟨C + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 e, k⟩ :=
  (h.cs.sub_left (Offset.sub_base _ hd)).sub_right (Offset.sub_base _ he)

theorem Env.st_st {d n e k : Nat} (hd : d + n ≤ e ∨ e + k ≤ d) (hn : d + n ≤ 80) (hk : e + k ≤ 80) :
    (⟨St + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨St + BitVec.ofNat 64 e, k⟩ :=
  Offset.disjoint _ hd (by have := h.sfit; omega) (by have := h.sfit; omega)

theorem Env.w_w {d n e k : Nat} (hd : d + n ≤ e ∨ e + k ≤ d) (hn : d + n ≤ 2560) (hk : e + k ≤ 2560) :
    (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ :=
  Offset.disjoint _ hd (by have := h.wfit; omega) (by have := h.wfit; omega)

/-- The address `St + d` does not wrap. -/
theorem Env.stToNat {d : Nat} (hd : d < 80) : (St + BitVec.ofNat 64 d).toNat = St.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (by have := h.sfit; omega)]

theorem Env.wToNat {d : Nat} (hd : d < 2560) : (W + BitVec.ofNat 64 d).toNat = W.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (by have := h.wfit; omega)]

end

/-- The regions the pieces write. -/
abbrev pieceRs (W St : Addr) : List Region := [stR St, wR W]

/-- A frame within part of `St` is within the pieces' regions. -/
theorem sub_st {St : Addr} {d n : Nat} (hd : d + n ≤ 80) (W : Addr) :
    ∃ r' ∈ pieceRs W St, Region.Sub ⟨St + BitVec.ofNat 64 d, n⟩ r' :=
  ⟨_, List.mem_cons_self .., Offset.sub_base _ hd⟩

theorem sub_w {W : Addr} {d n : Nat} (hd : d + n ≤ 2112) (St : Addr) :
    ∃ r' ∈ pieceRs W St, Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ r' :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub_base _ hd⟩

theorem sub_w0 {W : Addr} {n : Nat} (hn : n ≤ 2112) (St : Addr) :
    ∃ r' ∈ pieceRs W St, Region.Sub ⟨W, n⟩ r' :=
  ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix hn⟩

end VG.Proof.AesGcm.PPC64LE
