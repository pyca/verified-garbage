module

import VerifiedGarbage.Proof.Rsa.KeyWorkspace
public import VerifiedGarbage.Impl.Rsa.X86.KeyWs
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32

/-! # Workspace geometry and memory frames for i686 RSA key operations -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot

abbrev S (w : Nat) : Nat := 4 * (w + 2)
abbrev arr (w j : Nat) : Nat := hdr + j * S w
abbrev num (m : Mem) (B : Addr) (w j : Nat) : Nat := val32 m B (arr w j) w
abbrev slot (m : Mem) (B : Addr) (d : Nat) : Nat := w32 m B d

structure Ws (s : State) (B : Addr) (Z w N : Nat) : Prop where
  workspace : Scr s B Z
  fits : arr w N ≤ Z
  wpos : 0 < w
  wle : w ≤ 1024

theorem Ws.rest {s t : State} {B : Addr} {Z w N : Nat} {rs : List Reg}
    (h : Ws s B Z w N) (r : Keeps rs s t)
    (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : Ws t B Z w N :=
  { h with workspace := h.workspace.of_keeps r edi esp }

theorem arr_succ (w j : Nat) : arr w (j + 1) = arr w j + S w :=
  VG.Proof.Rsa.KeyWorkspace.arr_succ w j

theorem arr_mono {w j k : Nat} (h : j ≤ k) : arr w j ≤ arr w k :=
  VG.Proof.Rsa.KeyWorkspace.arr_mono h

theorem arr_end {w j k : Nat} (h : j < k) : arr w j + S w ≤ arr w k :=
  VG.Proof.Rsa.KeyWorkspace.arr_end h

theorem arr_disj {w j k : Nat} (h : j ≠ k) : arr w j + S w ≤ arr w k ∨ arr w k + S w ≤ arr w j :=
  VG.Proof.Rsa.KeyWorkspace.arr_disj h

theorem Ws.arr_fit {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) :
    arr w j + S w ≤ Z := Nat.le_trans (arr_end hj) h.fits

theorem Ws.fit64 {s : State} {B : Addr} {Z w N j : Nat} (h : Ws s B Z w N) (hj : j < N) :
    arr w j + S w ≤ 2 ^ 64 := by
  have := h.arr_fit hj; have := h.workspace.nowrap; omega

theorem Ws.hdr_le {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) : hdr ≤ Z :=
  Nat.le_trans (Nat.le_add_right _ _) h.fits

/-! ## Frames -/

/-- The bytes of the arrays `js` and the header words `ds`. -/
def ranges (w : Nat) (js ds : List Nat) : List (Nat × Nat) :=
  js.map (fun j => (arr w j, S w)) ++ ds.map (fun d => (d, 4))

/-- `m'` is `m` but on the arrays `js` and the header words `ds`. -/
def Keep (B : Addr) (w : Nat) (js ds : List Nat) (m m' : Mem) : Prop :=
  Outs B (ranges w js ds) m m'

theorem Keep.refl (B : Addr) (w : Nat) (js ds : List Nat) (m : Mem) : Keep B w js ds m m :=
  VG.Proof.Rsa.KeyWorkspace.Keep.refl B w js ds m

theorem Keep.trans {B : Addr} {w : Nat} {js ds : List Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Keep B w js ds m₁ m₂) (h₂ : Keep B w js ds m₂ m₃) : Keep B w js ds m₁ m₃ :=
  VG.Proof.Rsa.KeyWorkspace.Keep.trans h₁ h₂

theorem Keep.mono {B : Addr} {w : Nat} {js ds js' ds' : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') (hj : ∀ j ∈ js, j ∈ js' := by simp)
    (hd : ∀ d ∈ ds, d ∈ ds' := by simp) : Keep B w js' ds' m m' :=
  VG.Proof.Rsa.KeyWorkspace.Keep.mono h hj hd

/-- Two frames, each widened to the union. -/
theorem Keep.join {B : Addr} {w : Nat} {js₁ ds₁ js₂ ds₂ js ds : List Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Keep B w js₁ ds₁ m₁ m₂) (h₂ : Keep B w js₂ ds₂ m₂ m₃)
    (hj₁ : ∀ j ∈ js₁, j ∈ js := by simp) (hd₁ : ∀ d ∈ ds₁, d ∈ ds := by simp)
    (hj₂ : ∀ j ∈ js₂, j ∈ js := by simp) (hd₂ : ∀ d ∈ ds₂, d ∈ ds := by simp) :
    Keep B w js ds m₁ m₃ :=
  VG.Proof.Rsa.KeyWorkspace.Keep.join h₁ h₂ hj₁ hd₁ hj₂ hd₂

theorem Keep.of_arr {B : Addr} {w o n d : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Outside B (arr w o + d) n m m') (hn : d + n ≤ S w) (ho : o ∈ js) :
    Keep B w js ds m m' :=
  VG.Proof.Rsa.KeyWorkspace.Keep.of_arr h hn ho

theorem Keep.of_slot {B : Addr} {w e : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Outside B e 4 m m') (he : e ∈ ds) : Keep B w js ds m m' :=
  VG.Proof.Rsa.KeyWorkspace.Keep.of_slot h he

/-- An array outside the frame. -/
theorem Keep.num {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (fit : arr w j + S w ≤ 2 ^ 64) : num m' B w j = num m B w j :=
  VG.Proof.Rsa.KeyWorkspace.Keep.num h hj hd fit

/-- All the words of an array outside the frame. -/
theorem Keep.full {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {j : Nat} (hj : ∀ k ∈ js, k ≠ j) (hd : ∀ d ∈ ds, d + 4 ≤ hdr)
    (fit : arr w j + S w ≤ 2 ^ 64) :
    val32 m' B (arr w j) (w + 2) = val32 m B (arr w j) (w + 2) :=
  VG.Proof.Rsa.KeyWorkspace.Keep.full h hj hd fit

/-- A word of an array outside the frame. -/
theorem Keep.word {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {j i : Nat} (hi : 4 * i + 4 ≤ S w) (hj : ∀ k ∈ js, k ≠ j)
    (hd : ∀ d ∈ ds, d + 4 ≤ hdr) (fit : arr w j + S w ≤ 2 ^ 64) :
    w32 m' B (arr w j + 4 * i) = w32 m B (arr w j + 4 * i) :=
  VG.Proof.Rsa.KeyWorkspace.Keep.word h hi hj hd fit

/-- A header word outside the frame. -/
theorem Keep.slot {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {e : Nat} (he : e + 4 ≤ hdr) (hd : ∀ d ∈ ds, e + 4 ≤ d ∨ d + 4 ≤ e) :
    slot m' B e = slot m B e :=
  VG.Proof.Rsa.KeyWorkspace.Keep.slot h he hd

/-- Memory outside the working space. -/
theorem Keep.out {B : Addr} {w : Nat} {js ds : List Nat} {m m' : Mem}
    (h : Keep B w js ds m m') {Z : Nat} (hj : ∀ j ∈ js, arr w j + S w ≤ Z) (hd : ∀ d ∈ ds, d + 4 ≤ Z)
    {x : Addr} (hx : Z ≤ ofs B x) : m' x = m x :=
  VG.Proof.Rsa.KeyWorkspace.Keep.out h hj hd hx

end VG.Proof.Rsa.X86.Keys
