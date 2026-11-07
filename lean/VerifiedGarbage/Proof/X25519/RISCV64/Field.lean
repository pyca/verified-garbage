module
public import VerifiedGarbage.Impl.X25519.RISCV64
public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
public import VerifiedGarbage.Proof.X25519.Limbs
import VerifiedGarbage.Proof.X25519.RISCV64.Pass
public import VerifiedGarbage.Proof.X25519.Field

import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.TCB.RISCV64.Isa

/-!
# X25519 on RISCV64: field elements in the working space

A field element is 8 words at an offset `o` of the working space at `B`
(`limb`), for the number `V` and its residue `FS`; every limb is below `2³²`
as a word.
-/

@[expose] public section

namespace VG.Proof.X25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X25519.RISCV64
open VG.Spec.X25519 (P Fe)

/-- `a3` holds the working space `b`, a multiple of 8 (the working space
rounded up), followed by at least 2048 writable bytes, all that offsets in
the immediates of loads and stores reach. -/
structure Ctx (b : Addr) (s : State) : Prop where
  a3 : s.gpr .a3 = b
  al : b.toNat % 8 = 0
  wr : ∀ d n, d + n ≤ 2048 → InRegions s.wr (b + BitVec.ofNat 64 d) n

theorem Ctx.of_rest {b : Addr} {s s' : State} {ws : List Reg} (h : Ctx b s) (hr : Rest ws s s')
    (h6 : Reg.a3 ∉ ws) : Ctx b s' :=
  ⟨by rw [hr.gpr _ h6, h.a3], h.al, by rw [hr.wr]; exact h.wr⟩

theorem Ctx.inW {b : Addr} {s : State} (h : Ctx b s) {d n : Nat} (hd : d + n ≤ 2048) :
    InRegions s.wr (b + BitVec.ofNat 64 d) n :=
  h.wr d n hd

theorem Ctx.inR {b : Addr} {s : State} (h : Ctx b s) {d n : Nat} (hd : d + n ≤ 2048) :
    InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 d) n :=
  let ⟨r, hr, hc⟩ := h.wr d n hd
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- Limb `k` of the element at `o`. -/
def limb (m : Mem) (B : Addr) (o k : Nat) : Nat := wd m B (o + 4 * k)

theorem limb_lt (m : Mem) (B : Addr) (o k : Nat) : limb m B o k < 2 ^ 32 := wd_lt _ _ _

/-- The number of the element at `o`. -/
def V (m : Mem) (B : Addr) (o : Nat) : Nat := val32 (limb m B o) 8

/-- The element at `o`. -/
def FS (m : Mem) (B : Addr) (o : Nat) : Fe := Proof.X25519.toFe (V m B o)

theorem V_lt (m : Mem) (B : Addr) (o : Nat) : V m B o < 2 ^ 256 :=
  val32_lt fun k _ => limb_lt m B o k

/-- The limbs of an element in a frame that does not overlap it. -/
theorem limb_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {B : Addr} {o : Nat}
    (hd : ∀ r ∈ rs, ∀ k < 8, (⟨B + BitVec.ofNat 64 (o + 4 * k), 4⟩ : Region).Disjoint r) :
    ∀ k < 8, limb m' B o k = limb m B o k := fun k hk => wd_frame hf fun r hr => hd r hr k hk

/-- The clobbered registers of the field operations. -/
abbrev clob : List Reg := [.a1, .a2, .a4, .a5, .a6, .a7, .t0]

/-! ## Loading and storing a limb -/

theorem lw0_ok {b : Addr} {s : State} (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 4 ≤ 2048)
    (hd4 : d % 4 = 0) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t ((s.mem.readW (b + BitVec.ofNat 64 d) 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .w t .a3 d :: is)) s Q :=
  wp_lw (by omega_using [hd]) (by rw [hc.a3]) (al4 hc.al hd4) (hc.inR hd) k

theorem sw0_ok {b : Addr} {s : State} (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 4 ≤ 2048)
    (hd4 : d % 4 = 0) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd s s' (s.mem.writeW (b + BitVec.ofNat 64 d) ((s.gpr t).setWidth 32)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.store .w t .a3 d :: is)) s Q :=
  wp_stw (by omega_using [hd]) (by rw [hc.a3]) (al4 hc.al hd4) (hc.inW hd) k

theorem ldSrc_ok {b : Addr} {o k : Nat} {s : State} (hc : Ctx b s) (hd : o + 4 * k + 4 ≤ 2048)
    (ho4 : o % 4 = 0) :
    WP isa (.block (ldSrc o k)) s fun s' =>
      (s'.gpr .a4).toNat = wd s.mem b (o + 4 * k) ∧ Rest [.a4] s s' ∧ s'.mem = s.mem :=
  lw0_ok hc hd (by omega_using [ho4]) fun s1 u1 => WP.block_nil ⟨by rw [u1.gpr, toNat_ext32]; rfl, u1.rest (by decide), u1.mem⟩

/-! ## The prologue -/

theorem prologue_ok {s : State} :
    WP isa (.block prologue) s fun s' =>
      s'.gpr .a7 = 38 ∧ s'.gpr .a5 = 0 ∧ Rest [.a5, .a7] s s' ∧ s'.mem = s.mem := by
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => WP.block_nil ⟨?_, u2.gpr, ?_, ?_⟩
  · rw [u2.other _ (by decide), u1.gpr]; rfl
  · exact (u1.rest (by decide)).trans (u2.rest (by decide))
  · rw [u2.mem, u1.mem]

end VG.Proof.X25519.RISCV64
