module
public import VerifiedGarbage.Impl.X25519.PPC64LE
public import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
public import VerifiedGarbage.Proof.X25519.PPC64LE.Limbs
import VerifiedGarbage.Proof.X25519.PPC64LE.Pass
public import VerifiedGarbage.Proof.X25519.Field

import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.X25519
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# X25519 on PPC64LE: field elements in the working space

A field element is 8 words at an offset `o` of the working space at `B`
(`limb`), for the number `V` and its residue `FS`; every limb is below `2³²`
as a word.
-/

@[expose] public section

namespace VG.Proof.X25519.PPC64LE

open VG VG.PPC64LE VG.Impl.X25519.PPC64LE
open VG.Spec.X25519 (P Fe)

/-- `r6` holds the working space `b`, at least 4096 writable bytes: X25519's
has 4096, Ed25519's on PPC64LE 8192. -/
structure Ctx (b : Addr) (s : State) : Prop where
  r6 : s.gpr .r6 = b
  wr : ∃ n, 4096 ≤ n ∧ (⟨b, n⟩ : Region) ∈ s.wr

theorem Ctx.of_rest {b : Addr} {s s' : State} {ws : List Reg} (h : Ctx b s) (hr : Rest ws s s')
    (h6 : Reg.r6 ∉ ws) : Ctx b s' :=
  ⟨by rw [hr.gpr _ h6, h.r6], by rw [hr.wr]; exact h.wr⟩

theorem Ctx.inW {b : Addr} {s : State} (h : Ctx b s) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions s.wr (b + BitVec.ofNat 64 d) n := by
  obtain ⟨k, hk, hw⟩ := h.wr
  exact in_base hw (by omega_using [hd, hk]) (by omega_using [hd])

theorem Ctx.inR {b : Addr} {s : State} (h : Ctx b s) {d n : Nat} (hd : d + n ≤ 4096) :
    InRegions (s.rd ++ s.wr) (b + BitVec.ofNat 64 d) n := by
  obtain ⟨k, hk, hw⟩ := h.wr
  exact in_base (List.mem_append_right _ hw) (by omega_using [hd, hk]) (by omega_using [hd])

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
abbrev clob : List Reg := [.r4, .r5, .r7, .r8, .r9, .r10, .r11]

/-! ## Loading and storing a limb -/

theorem lw0_ok {b : Addr} {s : State} (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 4 ≤ 4096)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' t ((s.mem.readW (b + BitVec.ofNat 64 d) 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .w t .r6 d :: is)) s Q :=
  wp_lw (by decide) (by omega_using [hd]) (by rw [hc.r6]) (hc.inR hd) k

theorem sw0_ok {b : Addr} {s : State} (hc : Ctx b s) {t : Reg} {d : Nat} (hd : d + 4 ≤ 4096)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Mupd s s' (s.mem.writeW (b + BitVec.ofNat 64 d) ((s.gpr t).setWidth 32)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.store .w t .r6 d :: is)) s Q :=
  wp_sw (by decide) (by omega_using [hd]) (by rw [hc.r6]) (hc.inW hd) k

theorem ldSrc_ok {b : Addr} {o k : Nat} {s : State} (hc : Ctx b s) (hd : o + 4 * k + 4 ≤ 4096) :
    WP isa (.block (ldSrc o k)) s fun s' =>
      (s'.gpr .r7).toNat = wd s.mem b (o + 4 * k) ∧ Rest [.r7] s s' ∧ s'.mem = s.mem :=
  lw0_ok hc hd fun s1 u1 => WP.block_nil ⟨by rw [u1.gpr, toNat_ext32]; rfl, u1.rest (by decide), u1.mem⟩

/-! ## The prologue -/

theorem prologue_ok {s : State} :
    WP isa (.block prologue) s fun s' =>
      s'.gpr .r10 = 38 ∧ s'.gpr .r8 = 0 ∧ Rest [.r8, .r10] s s' ∧ s'.mem = s.mem := by
  refine wp_li (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => WP.block_nil ⟨?_, u2.gpr, ?_, ?_⟩
  · rw [u2.other _ (by decide), u1.gpr]; rfl
  · exact (u1.rest (by decide)).trans (u2.rest (by decide))
  · rw [u2.mem, u1.mem]

end VG.Proof.X25519.PPC64LE
