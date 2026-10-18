module

public import VerifiedGarbage.Proof.Rsa.X86.RvZero
public import VerifiedGarbage.Proof.Rsa.X86.RvProductCore
public import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.Rsa.Octets
public import VerifiedGarbage.Proof.Dsa.Frame

/-! # Importing the three key integers into the recovery workspace -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

def inputBytes (g : CallGeometry) (m : Mem) (i : Fin 3) : List Byte :=
  Spec.Rsa.bytesAt m (g.buffer (4 + 2 * i.val)).base (g.buffer (4 + 2 * i.val)).len

def inputValue (g : CallGeometry) (m : Mem) (i : Fin 3) : Nat := Spec.Rsa.os2ip (inputBytes g m i)

theorem inputValue_lt (g : CallGeometry) (m : Mem) (i : Fin 3) :
    inputValue g m i < 2 ^ (8 * (g.buffer (4 + 2 * i.val)).len) := by
  have h := VG.Proof.Rsa.lt_of_os2ip (inputBytes g m i)
  simpa only [inputValue, inputBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range,
    show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul] using h

theorem Inputs.inputFrame {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s)
    (frame : Frame g.writes m m') (i : Fin 3) : inputBytes g m' i = inputBytes g m i :=
  VG.Proof.Rsa.rsa_bytes_frame frame (by have := h.inputBound i; have := h.upper; omega) (h.inputApart i)

structure LS (g : CallGeometry) (s0 : State) (A : Nat → Nat) (s : State) : Prop where
  inputs : Inputs g s
  frame : Outside g.B 16 (g.Z - 16) s0.mem s.mem
  rest : Keeps opRegs s0 s
  full : ∀ j < nArr, val32 s.mem g.B (arr g.toGeo.w j) (g.toGeo.w + 2) = A j

theorem LS.load {g : CallGeometry} {s0 s : State} {A : Nat → Nat} (h : LS g s0 A s)
    (i : Fin 3) {j : Nat} (hj : j < nArr) :
    WP isa (load g.n (4 + 2 * i.val) j) s fun t => LS g s0 (upd A j (inputValue g s0.mem i)) t := by
  refine WP.mono (load_ok h.inputs i hj) fun t ⟨inputs, k, v, r⟩ => ?_
  have value : val32 t.mem g.B (arr g.toGeo.w j) (g.toGeo.w + 2) = inputValue g s0.mem i := by
    change _ = Spec.Rsa.os2ip (inputBytes g s.mem i) at v
    rw [h.inputs.inputFrame (h.inputs.scratchFrame h.frame) i] at v
    exact v
  refine ⟨inputs, h.frame.trans (h.inputs.keepBody k (by simpa using hj) (by simp)), h.rest.trans r, ?_⟩
  intro l hl
  by_cases eq : l = j
  · subst l; rw [upd_self]; exact value
  · rw [upd_ne _ _ eq, k.full (by simpa using Ne.symm eq) (by simp) (h.inputs.ws.fit64 hl), h.full l hl]

theorem zero_ls {g : CallGeometry} {s : State} (h : Inputs g s) :
    WP isa (VG.Impl.Mont.X86.Dynamic.zerosW hdr (nArr * (g.toGeo.w + 2))) s (LS g s (fun _ => 0)) := by
  refine WP.mono (zeroArrays_ok h) fun t ⟨ht, f, z, r⟩ => ?_
  have fit := h.ws.fits
  change hdr + nArr * (4 * (g.toGeo.w + 2)) ≤ g.Z at fit
  refine ⟨ht, f.mono (by unfold hdr; omega) ?_, r.mono (by decide), z⟩
  have fit' : hdr + 4 * (nArr * (g.toGeo.w + 2)) ≤ g.Z := by simpa only [Nat.mul_left_comm] using fit
  have := h.ws.hdr_le
  unfold hdr at *
  omega

def Aload (n e d : Nat) : Nat → Nat := upd (upd (upd (fun _ => 0) aN n) (2 * wE) e) (2 * wD) d

theorem loads_ls {g : CallGeometry} {s : State} (h : Inputs g s) :
    WP isa (loads g.n) s (LS g s (Aload (inputValue g s.mem 0) (inputValue g s.mem 1) (inputValue g s.mem 2))) := by
  unfold loads
  simp only [seqs]
  refine WP.seq (WP.mono (zero_ls h) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (h1.load 0 (j := aN) (by decide)) fun s2 h2 => ?_)
  refine WP.seq (WP.mono (h2.load 1 (j := 2 * wE) (by decide)) fun s3 h3 => ?_)
  exact h3.load 2 (j := 2 * wD) (by decide)

theorem LS.number {g : CallGeometry} {s0 s : State} {A : Nat → Nat} (h : LS g s0 A s)
    {j : Nat} (hj : j < nArr) (bound : A j < 2 ^ (32 * g.toGeo.w)) :
    num s.mem g.B g.toGeo.w j = A j := by
  rw [← h.full j hj] at bound ⊢
  exact VG.Proof.Dsa.val32_prefix_of_lt (by omega) bound

theorem LS.wide {g : CallGeometry} {s0 s : State} {A : Nat → Nat} (h : LS g s0 A s)
    {j : Nat} (hj : j < 22) (zero : A (2 * j + 1) = 0) :
    num s.mem g.B g.toGeo.W j = A (2 * j) := by
  apply numW_of (h.full (2 * j) (by unfold nArr; omega))
  rw [h.number (by unfold nArr; omega) (by rw [zero]; exact Nat.two_pow_pos _), zero]

theorem loads_ok {g : CallGeometry} {s : State} (h : Inputs g s) :
    WP isa (loads g.n) s fun t =>
      KS g.toGeo s (fun _ => inputValue g s.mem 0) [aN]
        (AW1 (inputValue g s.mem 1) (inputValue g s.mem 2)) [wZ, wE, wD, wM, wMod]
        (fun _ => 0) [] t := by
  refine WP.mono (loads_ls h) fun t ht => ?_
  refine ⟨ht.inputs.ws, h.lower, h.upper, ht.frame, ht.rest, ?_, ?_, by simp,
    by decide, by decide, by simp⟩
  · intro j hj
    simp only [List.mem_singleton] at hj
    subst j
    have value : Aload (inputValue g s.mem 0) (inputValue g s.mem 1) (inputValue g s.mem 2) aN =
        inputValue g s.mem 0 := rfl
    rw [ht.number (by decide) ?_, value]
    rw [value]
    apply Nat.lt_of_lt_of_le (inputValue_lt g s.mem 0)
    apply Nat.pow_le_pow_right (by decide)
    have := h.inputBound 0
    change 8 * (g.buffer (4 + 2 * (0 : Fin 3).val)).len ≤ 32 * (2 * g.n + 2)
    omega
  · intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rw [ht.wide (by decide) (by simp [Aload, upd, wZ, wE, wD, wM, wMod, aN])] <;> rfl

end VG.Proof.Rsa.X86.Recover
