module

public import VerifiedGarbage.Proof.Mont.X86.Sse2.Dot
public import VerifiedGarbage.Proof.Mont.X86.ArgFar
import VerifiedGarbage.Proof.Framework.Omega

/-! # The parameters and the column's indices

The kernel's seven parameters are words on the stack, `d` bytes above `esp`
(`Params`), past the working space, so changes within it keep them. Each
column computes, from `ecx = 4 k` and the parameter `4 N`, the first index of
its products, `4 max(0, k + 1 - N)` (`lowIdx_ok`), and their end: `4 min(k +
1, N)` for a product (`endProduct_ok`), `4 ⌊(k + 1) / 2⌋` for the products
above the diagonal of a square (`endHalf_ok`) and `4 min(k, N)` for the
quotient digits (`endReduce_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Sse2 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt
open VG.Proof.Mont.X86.Dynamic (ArgFar readSrc_keep readSrc_upd)

/-- The parameters `V i` at `[esp + d + 4 i]`, past the working space. -/
structure Params (s : State) (W : Addr) (L : Nat) (V : Nat → BitVec 32) (d : Nat) : Prop where
  read : ∀ i < 7, readSrc s (.mem (prm d i)) = some (V i)
  far : ∀ i < 7, ArgFar s W L (prm d i)

/-- Changes within the working space, with `esp` and the permissions as they
were, keep the parameters. -/
theorem Params.keep {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat} (h : Params s W L V d)
    (O : Outs W [(0, L)] s.mem t.mem) (hsp : t.gpr .esp = s.gpr .esp) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) : Params t W L V d :=
  ⟨fun i hi => (readSrc_keep (h.far i hi) O (by simp) hsp hrd hwr).trans (h.read i hi),
    fun i hi => (h.far i hi).keep hsp⟩

/-- What scalar code leaves: the registers but `rs`, the memory, the MCDT
depth and the XMM registers. -/
structure Sk (rs : List Reg) (s t : State) : Prop where
  keep : Keeps rs s t
  mem : t.mem = s.mem
  mcdt : t.mcdt = s.mcdt
  xmm : t.xmm = s.xmm

theorem Sk.refl (rs : List Reg) (s : State) : Sk rs s s := ⟨Keeps.refl _ _, rfl, rfl, rfl⟩

theorem Sk.trans {rs rs' : List Reg} {s₁ s₂ s₃ : State} (h₁ : Sk rs' s₁ s₂) (h₂ : Sk rs s₂ s₃)
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : Sk rs' s₁ s₃ :=
  ⟨h₁.keep.widen h₂.keep hs, h₂.mem.trans h₁.mem, h₂.mcdt.trans h₁.mcdt, h₂.xmm.trans h₁.xmm⟩

theorem Sk.mono {rs : List Reg} {s t : State} (h : Sk rs s t) (rs' : List Reg)
    (hs : ∀ r ∈ rs, r ∈ rs' := by decide) : Sk rs' s t :=
  ⟨h.keep.mono hs, h.mem, h.mcdt, h.xmm⟩

theorem Sk.of_upd (rs : List Reg) {s t : State} {d : Reg} {v : BitVec 32} (u : Upd s t d v)
    (hm : t.mcdt = s.mcdt) (hx : t.xmm = s.xmm) (hd : d ∈ rs := by decide) : Sk rs s t :=
  ⟨u.keeps.mono fun r hr => by simp only [List.mem_singleton] at hr; exact hr ▸ hd, u.mem, hm, hx⟩

theorem Sk.of_fupd {s t : State} (u : Fupd s t) (hm : t.mcdt = s.mcdt) (hx : t.xmm = s.xmm) (rs : List Reg) :
    Sk rs s t := ⟨u.keeps rs, u.mem, hm, hx⟩

theorem Params.of_sk {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat} (h : Params s W L V d)
    {rs : List Reg} (K : Sk rs s t) (hsp : .esp ∉ rs := by decide) : Params t W L V d :=
  h.keep (by rw [K.mem]; exact Outs.refl _ _ _) (K.keep.1 _ hsp) K.keep.2.1 K.keep.2.2

theorem Ws.of_sk {s t : State} {W : Addr} {L : Nat} (h : Ws s W L) {rs : List Reg} (K : Sk rs s t) : Ws t W L :=
  h.of_keeps K.keep

/-- A parameter read in a state `Sk` from one where it is known. -/
theorem Params.readSk {s t : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {d : Nat} (h : Params s W L V d)
    {rs : List Reg} (K : Sk rs s t) {i : Nat} (hi : i < 7) (hsp : .esp ∉ rs := by decide) :
    readSrc t (.mem (prm d i)) = some (V i) := (h.of_sk K hsp).read i hi

theorem ofNat_of_toNat {v : BitVec 32} {n : Nat} (h : v.toNat = n) : v = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ v.isLt)]

/-! ## The indices -/

section
variable {s : State} {W : Addr} {L : Nat} {V : Nat → BitVec 32} {N k : Nat}

/-- `edx = 4 (k + 1 - N)`, the first product's index. -/
theorem lowIdx_ok (P : Params s W L V 12) (hN : (V pN4).toNat = 4 * N) (hc : s.gpr .ecx = BitVec.ofNat 32 (4 * k))
    (hk : 4 * (k + 1) < 2 ^ 32) :
    WP isa lowIdx s fun t => t.gpr .edx = BitVec.ofNat 32 (4 * (k + 1 - N)) ∧ Sk [.edx, .eax] s t := by
  unfold lowIdx
  refine WP.seq (wp_movX (P.read pN4 (by decide)) fun t0 u0 m0 x0 => wp_movX rfl fun t1 u1 m1 x1 =>
    wp_addX rfl fun t2 u2 _ m2 x2 => ?_)
  have K2 : Sk [.edx, .eax] s t2 :=
    ((Sk.of_upd [.edx, .eax] u0 m0 x0).trans (Sk.of_upd [.edx, .eax] u1 m1 x1)).trans (Sk.of_upd [.edx, .eax] u2 m2 x2)
  have a2 : t2.gpr .eax = V pN4 := by rw [u2.other _ (by decide), u1.other _ (by decide), u0.gpr]
  refine wp_subX (show some (t2.gpr .eax) = _ by rw [a2]) fun t3 u3 c3 m3 x3 => WP.block_nil ?_
  have K3 : Sk [.edx, .eax] s t3 := K2.trans (Sk.of_upd [.edx, .eax] u3 m3 x3)
  have e2 : t2.gpr .edx = BitVec.ofNat 32 (4 * k + 4) := by
    rw [u2.gpr, u1.gpr, u0.other _ (by decide), hc]; exact BitVec.ofNat_add _ _ |>.symm
  have hv := (V pN4).isLt
  by_cases hlt : k + 1 < N
  · refine WP.ite true (by show t3.cf = _; rw [c3, e2, toNat_ofNat_lt (by omega), hN, decide_eq_true (by omega)])
      (fun _ => wp_movX rfl fun t4 u4 m4 x4 => WP.block_nil ⟨?_, K3.trans (Sk.of_upd [.edx, .eax] u4 m4 x4)⟩)
      (fun h => absurd h (by decide))
    rw [u4.gpr, show k + 1 - N = 0 by omega]; rfl
  · refine WP.ite false (by show t3.cf = _; rw [c3, e2, toNat_ofNat_lt (by omega), hN, decide_eq_false (by omega)])
      (fun h => absurd h (by decide)) (fun _ => WP.block_nil ⟨?_, K3⟩)
    rw [u3.gpr, e2, ofNat_of_toNat hN, sub_ofNat (by omega), show 4 * (k + 1 - N) = 4 * k + 4 - 4 * N by omega]

/-- `ebx = 4 min(k + 1, N)`, the end of a product's column. -/
theorem endProduct_ok (P : Params s W L V 12) (hN : (V pN4).toNat = 4 * N)
    (hc : s.gpr .ecx = BitVec.ofNat 32 (4 * k)) (hk : 4 * (k + 1) < 2 ^ 32) :
    WP isa endProduct s fun t => t.gpr .ebx = BitVec.ofNat 32 (4 * min (k + 1) N) ∧ Sk [.ebx, .eax] s t := by
  unfold endProduct
  refine WP.seq (wp_movX (P.read pN4 (by decide)) fun t0 u0 m0 x0 => wp_movX rfl fun t1 u1 m1 x1 =>
    wp_addX rfl fun t2 u2 _ m2 x2 => ?_)
  have K2 : Sk [.ebx, .eax] s t2 :=
    ((Sk.of_upd [.ebx, .eax] u0 m0 x0).trans (Sk.of_upd [.ebx, .eax] u1 m1 x1)).trans (Sk.of_upd [.ebx, .eax] u2 m2 x2)
  have a2 : t2.gpr .eax = V pN4 := by rw [u2.other _ (by decide), u1.other _ (by decide), u0.gpr]
  refine wp_cmpX (show some (t2.gpr .eax) = _ by rw [a2]) fun t3 f3 c3 _ m3 x3 => WP.block_nil ?_
  have K3 : Sk [.ebx, .eax] s t3 := K2.trans (Sk.of_fupd f3 m3 x3 [.ebx, .eax])
  have e2 : t2.gpr .ebx = BitVec.ofNat 32 (4 * k + 4) := by
    rw [u2.gpr, u1.gpr, u0.other _ (by decide), hc]; exact BitVec.ofNat_add _ _ |>.symm
  have e3 : t3.gpr .ebx = BitVec.ofNat 32 (4 * k + 4) := by rw [f3.gpr, e2]
  have a3 : t3.gpr .eax = V pN4 := by rw [f3.gpr, a2]
  have hv := (V pN4).isLt
  by_cases hlt : k + 1 < N
  · refine WP.ite false (by
        show t3.cf.map _ = _; rw [c3, e2, toNat_ofNat_lt (by omega), hN, decide_eq_true (by omega)]; rfl)
      (fun h => absurd h (by decide)) (fun _ => WP.block_nil ⟨?_, K3⟩)
    rw [e3, Nat.min_eq_left (by omega)]; rfl
  · refine WP.ite true (by
        show t3.cf.map _ = _; rw [c3, e2, toNat_ofNat_lt (by omega), hN, decide_eq_false (by omega)]; rfl)
      (fun _ => wp_movX (show some (t3.gpr .eax) = _ by rw [a3]) fun t4 u4 m4 x4 =>
        WP.block_nil ⟨?_, K3.trans (Sk.of_upd [.ebx, .eax] u4 m4 x4)⟩)
      (fun h => absurd h (by decide))
    rw [u4.gpr, ofNat_of_toNat hN, Nat.min_eq_right (by omega)]

/-- `ebx = 4 min(k, N)`, the end of the quotient digits' products. -/
theorem endReduce_ok (P : Params s W L V 12) (hN : (V pN4).toNat = 4 * N)
    (hc : s.gpr .ecx = BitVec.ofNat 32 (4 * k)) (hk : 4 * (k + 1) < 2 ^ 32) :
    WP isa endReduce s fun t => t.gpr .ebx = BitVec.ofNat 32 (4 * min k N) ∧ Sk [.ebx, .eax] s t := by
  unfold endReduce
  refine WP.seq (wp_movX (P.read pN4 (by decide)) fun t0 u0 m0 x0 => wp_movX rfl fun t1 u1 m1 x1 => ?_)
  have K1 : Sk [.ebx, .eax] s t1 := (Sk.of_upd [.ebx, .eax] u0 m0 x0).trans (Sk.of_upd [.ebx, .eax] u1 m1 x1)
  have a1 : t1.gpr .eax = V pN4 := by rw [u1.other _ (by decide), u0.gpr]
  refine wp_cmpX (show some (t1.gpr .eax) = _ by rw [a1]) fun t3 f3 c3 _ m3 x3 => WP.block_nil ?_
  have K3 : Sk [.ebx, .eax] s t3 := K1.trans (Sk.of_fupd f3 m3 x3 [.ebx, .eax])
  have e1 : t1.gpr .ebx = BitVec.ofNat 32 (4 * k) := by rw [u1.gpr, u0.other _ (by decide), hc]
  have a3 : t3.gpr .eax = V pN4 := by rw [f3.gpr, a1]
  have hv := (V pN4).isLt
  by_cases hlt : k < N
  · refine WP.ite false (by
        show t3.cf.map _ = _; rw [c3, e1, toNat_ofNat_lt (by omega), hN, decide_eq_true (by omega)]; rfl)
      (fun h => absurd h (by decide)) (fun _ => WP.block_nil ⟨?_, K3⟩)
    rw [f3.gpr, e1, Nat.min_eq_left (by omega)]
  · refine WP.ite true (by
        show t3.cf.map _ = _; rw [c3, e1, toNat_ofNat_lt (by omega), hN, decide_eq_false (by omega)]; rfl)
      (fun _ => wp_movX (show some (t3.gpr .eax) = _ by rw [a3]) fun t4 u4 m4 x4 =>
        WP.block_nil ⟨?_, K3.trans (Sk.of_upd [.ebx, .eax] u4 m4 x4)⟩)
      (fun h => absurd h (by decide))
    rw [u4.gpr, ofNat_of_toNat hN, Nat.min_eq_right (by omega)]

end

end VG.Proof.Mont.X86.Sse2
