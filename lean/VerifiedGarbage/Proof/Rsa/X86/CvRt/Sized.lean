module

public import VerifiedGarbage.Proof.Rsa.X86.BatchLaw
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
public import VerifiedGarbage.Proof.Rsa.X86.CvRt.Load
import VerifiedGarbage.Proof.Bignum.ByteWords
import VerifiedGarbage.Proof.Bignum.ReadPrefix
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Load
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Rsa.X86.InvParts
public import VerifiedGarbage.Impl.Rsa.X86.Inverse
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Spec.Rsa
import VerifiedGarbage.Proof.Bignum.MemoryFrame
import VerifiedGarbage.Proof.Rsa.X86.CvRt.Core
import VerifiedGarbage.Proof.Rsa.X86.CvFrames

/-! ### `Rsa.X86.CvRt.Store`, which only this module used -/

section

/-! # CRT parameter calculation at a run-time width: the outputs

`store_ok` clears an array unless the checks passed and writes its low bytes,
big-endian, to an output; `stores_ok` writes the three and returns the mask.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Bignum.X86 (reverseBytes PublicFn.argument)
open VG.Impl.Rsa.X86.Keys (aM aNM aZero aT1 aT2 aT3 aT4 sOdd sB sC sT hdr seqs)
open VG.Impl.Rsa.X86.KeyRt (Lay arrPtr)
open VG.Impl.Rsa.X86.CrtValues (sPodd sE1 sE2 sE3 sMask aOne aQ aP aDQ aDR aDD aDT aDR2 aDR3 aD nArr)
open VG.Impl.Rsa.X86.CrtValuesRt
open VG.Proof.Rsa.X86.Keys (Ws Keep arr num S slot ranges wp_seqs_cons)
open VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.CrtValues (CallGeometry Inputs inputBytes bodyWrites)

theorem output_word {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (i : Fin 3)
    (f : Frame [g.buffer (2 * i.val)] m m') {d : Nat} (bound : d + 4 ≤ g.size) :
    w32 m' g.base d = w32 m g.base d := by
  unfold w32
  rw [f.readW (r := ⟨g.base, g.size⟩) (a := off g.base d) (w := 32)
    (Scr.contains h.ws.workspace.nowrap bound)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact (h.outputScratch i).symm) (by decide)]

theorem output_num {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (len : Lengths g) (i : Fin 3)
    (f : Frame [g.buffer (2 * i.val)] m m') {j : Nat} (hj : j < nArr) :
    num m' g.base (kw (g.args 7).toNat) j = num m g.base (kw (g.args 7).toNat) j := by
  apply val32_congr
  intro k hk
  obtain fits := (inputsRt h len).ws.arr_fit hj
  unfold S at fits
  exact output_word h i f (by omega_using [hk, fits])

theorem store_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) (i : Fin 3) {j : Nat}
    (hj : j < nArr) (hjz : j ≠ aZero) (zero : num s.mem g.base (kw (g.args 7).toNat) aZero = 0) (accept : Bool)
    (mask : slot s.mem g.base sMask = if accept then 1 else 0) :
    WP isa (store (2 * i.val) j) s fun t =>
      Inputs g t ∧
      Spec.Rsa.bytesAt t.mem (g.buffer (2 * i.val)).base (g.buffer (2 * i.val)).len =
        Spec.Rsa.i2osp ((if accept then num s.mem g.base (kw (g.args 7).toNat) j else 0) %
          2 ^ (8 * (g.buffer (2 * i.val)).len)) (g.buffer (2 * i.val)).len ∧
      Frame [⟨off g.base (arr (kw (g.args 7).toNat) j), S (kw (g.args 7).toNat)⟩, g.buffer (2 * i.val)]
        s.mem t.mem ∧
      (∀ d, d + 4 ≤ hdr → slot t.mem g.base d = slot s.mem g.base d) ∧
      (∀ k, k < nArr → k ≠ j → num t.mem g.base (kw (g.args 7).toNat) k = num s.mem g.base (kw (g.args 7).toNat) k) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  obtain r := inputsRt h len
  obtain fits := r.ws.arr_fit hj
  have nw := r.ws.workspace.nowrap
  obtain fit64 := r.ws.fit64 hj
  have wd := len.width
  have up := h.upper
  obtain kwEq : kw (g.args 7).toNat = 2 * g.n := by rw [wd]
  have hi := i.isLt
  unfold store
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (sel_ok r hj (by decide) hj (by decide) (by rw [mask]; cases accept <;> decide) (.inl hjz))
    fun u ⟨ru, ku, vu, rku⟩ => ?_
  obtain outside := keep_outside r.ws ku (by simpa using hj) (by simp)
  obtain frameU := scratchFrame h outside
  obtain inputsU := h.after rku (by decide) (by decide) frameU
  obtain raw : Outside g.base (arr (kw (g.args 7).toNat) j) (S (kw (g.args 7).toNat)) s.mem u.mem := by
    intro a ha
    apply ku a
    intro r hr
    simp only [ranges, List.map_cons, List.map_nil, List.append_nil, List.mem_singleton] at hr
    subst r
    exact ha
  obtain ownFrame := outside_frame raw fit64
  obtain chosen : num u.mem g.base (kw (g.args 7).toNat) j =
      if accept then num s.mem g.base (kw (g.args 7).toNat) j else 0 := by
    rw [vu, mask, zero]; cases accept <;> rfl
  obtain positive := h.outputPositive i
  obtain bound := h.outputBound i
  obtain outFit := h.outputFit i
  obtain outWrite := h.outputWrite i
  obtain outScratch := h.outputScratch i
  simp only [CallGeometry.buffer] at positive bound outFit outWrite outScratch ⊢
  generalize hL : (g.args (2 * i.val + 1)).toNat = L at positive bound outFit outWrite outScratch ⊢
  obtain Lw : L ≤ 4 * kw (g.args 7).toNat := by omega_using [kwEq, bound]
  simp only [S] at fits
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (inputsU.arguments (2 * i.val) (by omega_using [])).readSrc fun u₁ U₁ _ => ?_
  obtain h₁ := inputsU.after U₁.keeps (by decide) (by decide) (by rw [U₁.mem]; exact Frame.refl _ _)
  refine wp_movS (h₁.arguments (2 * i.val + 1) (by omega_using [])).readSrc fun u₂ U₂ _ => ?_
  obtain K₂ : Keeps [.ebx, .ecx] u u₂ := (U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))
  obtain m₂ : u₂.mem = u.mem := by rw [U₂.mem, U₁.mem]
  obtain r₂ := ru.keep K₂ (by decide) (by decide) (by rw [m₂]; exact Outside.refl _ _ _ _)
  refine arrPtr_ok (lenSrc r₂) r₂.lenLe r₂.edi (by decide) (by decide) (by omega_using [fits, nw]) fun v Kv mv pv _ => ?_
  refine wp_addS rfl fun v₃ u₃ _ => wp_subS rfl fun v₄ u₄ _ => WP.block_nil ?_
  obtain srcAddr : byteAddr (v.gpr .esi) = off g.base (arr (kw (g.args 7).toNat) j) :=
    VG.Proof.Bignum.X86.PublicRt.byteAddr_ptr pv (by omega_using [fits, nw])
  obtain srcNat : (v.gpr .esi).toNat = g.base.toNat + arr (kw (g.args 7).toNat) j := by
    rw [pv, Nat.mod_eq_of_lt (by omega_using [fits, nw])]
  obtain K₄ : Keeps [.ebx, .ecx, .edx, .esi] u v₄ :=
    ((K₂.mono (by decide)).trans (Kv.mono (by decide))).trans ((u₃.keeps.mono (by decide)).trans
      (u₄.keeps.mono (by decide)))
  obtain m₄ : v₄.mem = u.mem := by rw [u₄.mem, u₃.mem, mv, m₂]
  obtain ecx₄ : v₄.gpr .ecx = BitVec.ofNat 32 L := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), Kv.1 _ (by decide), U₂.gpr, ← hL, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  obtain ebx₄ : v₄.gpr .ebx = g.args (2 * i.val) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), Kv.1 _ (by decide), U₂.other _ (by decide), U₁.gpr]
  obtain esi₄ : v₄.gpr .esi = v.gpr .esi + BitVec.ofNat 32 (L - 1) := by
    obtain ecx : v.gpr .ecx = BitVec.ofNat 32 L := by
      rw [Kv.1 _ (by decide), U₂.gpr, ← hL, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [u₄.gpr, u₃.gpr, ecx]
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc, ← BitVec.sub_eq_add_neg,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [positive])]
  obtain keepU : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s v₄ := (rku.mono (by decide)).trans (K₄.mono (by decide))
  obtain hsub : Region.Sub ⟨off g.base (arr (kw (g.args 7).toNat) j), L⟩ ⟨g.base, g.size⟩ := by
    have := Offset.sub g.base (d := arr (kw (g.args 7).toNat) j) (n := L) (e := 0) (k := g.size) (Nat.zero_le _)
      (by omega_using [fits, Lw])
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  refine WP.mono (reverseBuffer_ok v₄ (src := v.gpr .esi) (dst := g.args (2 * i.val)) (n := L) (by omega_using [positive])
    (by omega_arith) outFit (by omega_using [hL])
    (by rw [keepU.2.1, keepU.2.2, srcAddr]; exact r.ws.workspace.read (by omega_using [fits, Lw]))
    (by rw [keepU.2.2]; exact outWrite) (by rw [srcAddr]; exact outScratch.symm.sub_left hsub) ebx₄ esi₄ ecx₄)
    fun t ⟨V, F, _, T⟩ => ?_
  obtain F' : Frame [⟨byteAddr (g.args (2 * i.val)), L⟩] u.mem t.mem := by rw [← m₄]; exact F
  obtain all : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := keepU.trans (T.mono (by decide))
  obtain Fb : Frame [g.buffer (2 * i.val)] u.mem t.mem := by simpa [CallGeometry.buffer, hL] using F'
  obtain fullFrame : Frame g.writes s.mem t.mem :=
    frameU.trans (Fb.mono (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      obtain cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega_using []
      rcases cases with e | e | e <;> simp [CallGeometry.writes, e]))
  refine ⟨h.after all (by decide) (by decide) fullFrame, ?_, ?_, ?_, ?_, all⟩
  · rw [V, srcAddr, m₄, ← chosen]
    obtain eq : (u.mem.read (off g.base (arr (kw (g.args 7).toNat) j)) (4 * kw (g.args 7).toNat)).toNat =
        num u.mem g.base (kw (g.args 7).toNat) j := read_eq_val32 _ _ _ _
    rw [read_prefix u.mem _ (Lw), BitVec.toNat_setWidth, eq]
  · exact (ownFrame.mono (by simp)).trans (F'.mono (by simp))
  · intro d hd
    change w32 t.mem g.base d = w32 s.mem g.base d
    rw [output_word h i Fb (by have := r.ws.hdr_le; omega_using [hd, this])]
    exact ku.slot hd (by simp)
  · intro k hk ne
    rw [output_num h len i Fb hk]
    exact ku.num (by simpa using Ne.symm ne) (by simp) (r.ws.fit64 hk)

theorem storeFrame_body {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (len : Lengths g) (i : Fin 3)
    {j : Nat} (hj : j < nArr)
    (f : Frame [⟨off g.base (arr (kw (g.args 7).toNat) j), S (kw (g.args 7).toNat)⟩, g.buffer (2 * i.val)] m m') :
    Frame (bodyWrites g) m m' := by
  obtain r := inputsRt h len
  apply f.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨⟨off g.base 16, g.size - 16⟩, by simp [bodyWrites], Offset.sub g.base ?_ ?_⟩
    · have : hdr ≤ arr (kw (g.args 7).toNat) j := Nat.le_add_right _ _
      unfold hdr at this; omega_using [this]
    · have := r.ws.arr_fit hj
      have := r.ws.hdr_le
      unfold hdr at this; omega_arith
  · refine ⟨g.buffer (2 * i.val), ?_, fun _ hx => hx⟩
    obtain cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega_using []
    rcases cases with e | e | e <;> simp [bodyWrites, e]

theorem output_preserved {g : CallGeometry} {s : State} {m m' : Mem} (h : Inputs g s) (len : Lengths g)
    (i k : Fin 3) (ne : k ≠ i) {j : Nat} (hj : j < nArr)
    (f : Frame [⟨off g.base (arr (kw (g.args 7).toNat) j), S (kw (g.args 7).toNat)⟩, g.buffer (2 * i.val)] m m') :
    Spec.Rsa.bytesAt m' (g.buffer (2 * k.val)).base (g.buffer (2 * k.val)).len =
      Spec.Rsa.bytesAt m (g.buffer (2 * k.val)).base (g.buffer (2 * k.val)).len := by
  apply VG.Proof.Rsa.rsa_bytes_frame f (by have := h.outputBound k; have := h.upper; omega_arith)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (h.outputScratch k).sub_right (Offset.sub_base g.base ((inputsRt h len).ws.arr_fit hj))
  · exact h.outputSeparate k i ne

def resultBytes (g : CallGeometry) (m : Mem) (accept : Bool) (i : Fin 3) (j : Nat) : List Byte :=
  Spec.Rsa.i2osp ((if accept then num m g.base (kw (g.args 7).toNat) j else 0) %
    2 ^ (8 * (g.buffer (2 * i.val)).len)) (g.buffer (2 * i.val)).len

theorem stores_ok {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g)
    (zero : num s.mem g.base (kw (g.args 7).toNat) aZero = 0) (accept : Bool)
    (mask : slot s.mem g.base sMask = if accept then 1 else 0) :
    WP isa stores s fun t => Inputs g t ∧
      Spec.Rsa.bytesAt t.mem (g.buffer 0).base (g.buffer 0).len = resultBytes g s.mem accept 0 aDR2 ∧
      Spec.Rsa.bytesAt t.mem (g.buffer 2).base (g.buffer 2).len = resultBytes g s.mem accept 1 aDR3 ∧
      Spec.Rsa.bytesAt t.mem (g.buffer 4).base (g.buffer 4).len = resultBytes g s.mem accept 2 3 ∧
      t.gpr .eax = BitVec.ofNat 32 accept.toNat ∧ Frame (bodyWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  unfold stores
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok h len 0 (j := aDR2) (by decide) (by decide) zero accept mask)
    fun u ⟨hu, vu, fu, huHeader, huOther, ru⟩ => ?_
  obtain zeroU : num u.mem g.base (kw (g.args 7).toNat) aZero = 0 := by rw [huOther _ (by decide) (by decide), zero]
  obtain maskU : slot u.mem g.base sMask = if accept then 1 else 0 := by rw [huHeader _ (by decide), mask]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok hu len 1 (j := aDR3) (by decide) (by decide) zeroU accept maskU)
    fun v ⟨hv, vv, fv, hvHeader, hvOther, rv⟩ => ?_
  obtain zeroV : num v.mem g.base (kw (g.args 7).toNat) aZero = 0 := by rw [hvOther _ (by decide) (by decide), zeroU]
  obtain maskV : slot v.mem g.base sMask = if accept then 1 else 0 := by rw [hvHeader _ (by decide), maskU]
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (store_ok hv len 2 (j := 3) (by decide) (by decide) zeroV accept maskV)
    fun x ⟨hx, vx, fx, hxHeader, hxOther, rx⟩ => ?_
  obtain maskX : slot x.mem g.base sMask = if accept then 1 else 0 := by rw [hxHeader _ (by decide), maskV]
  refine wp_movS (readSrc_sc hx.ws.workspace (by have := hx.ws.hdr_le; unfold sMask hdr at *; omega_using [this]))
    fun t T _ => WP.block_nil ?_
  obtain frame : Frame (bodyWrites g) s.mem t.mem := by
    rw [T.mem]
    exact (storeFrame_body h len 0 (by decide) fu).trans
      ((storeFrame_body hu len 1 (by decide) fv).trans (storeFrame_body hv len 2 (by decide) fx))
  obtain all : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t :=
    ru.trans (rv.trans (rx.trans (T.keeps.mono (by decide))))
  refine ⟨hx.after T.keeps (by decide) (by decide) (by rw [T.mem]; exact Frame.refl _ _), ?_, ?_, ?_, ?_, frame, all⟩
  · rw [T.mem]
    exact (output_preserved hv len 2 0 (by decide) (by decide) fx).trans
      ((output_preserved hu len 1 0 (by decide) (by decide) fv).trans vu)
  · rw [T.mem]
    refine (output_preserved hv len 2 1 (by decide) (by decide) fx).trans ?_
    rw [huOther _ (by decide) (by decide)] at vv
    exact vv
  · rw [T.mem]
    rw [hvOther _ (by decide) (by decide), huOther _ (by decide) (by decide)] at vx
    exact vx
  · apply BitVec.eq_of_toNat_eq
    rw [T.gpr]
    change slot x.mem g.base sMask = _
    rw [maskX]; cases accept <;> rfl

end VG.Proof.Rsa.X86.CrtValuesRt

end

end


/-! # CRT parameter calculation at a run-time width, once the modulus is accepted

`sized_ok`: the inputs loaded, the arithmetic, and the outputs released
under the checks' mask, as `ArithmeticPost` states them.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.CrtValuesRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys (hdr seqs aZero)
open VG.Impl.Rsa.X86.CrtValues (sMask nArr)
open VG.Impl.Rsa.X86.CrtValuesRt
open VG.Proof.Rsa.X86.Keys (Keep num slot wp_seqs_cons)
open VG.Proof.Rsa.X86.KeyRt
open VG.Proof.Rsa.X86.CrtValues (CallGeometry Inputs inputBytes bodyWrites)

def encode (g : CallGeometry) (accept : Bool) (i : Fin 3) (x : Nat) : List Byte :=
  Spec.Rsa.i2osp ((if accept then x else 0) % 2 ^ (8 * (g.buffer (2 * i.val)).len)) (g.buffer (2 * i.val)).len

def ArithmeticPost (g : CallGeometry) (m : Mem) (t : State) : Prop :=
  let a := arithmeticGeometry g m
  ∃ V R₂ R₃ X : Nat,
    (1 < a.M → V = Nat.gcd a.Q a.M ∧ (a.M : Int) ∣ (X : Int) * a.Q - V ∧ X < a.M) ∧
    (a.P * a.Q = a.N → 0 < 2 * (a.P / 2) → R₂ = a.D % (2 * (a.P / 2))) ∧
    (a.P * a.Q = a.N → 0 < 2 * (a.Q / 2) → R₃ = a.D % (2 * (a.Q / 2))) ∧
    Spec.Rsa.bytesAt t.mem (g.buffer 0).base (g.buffer 0).len = encode g (maskOf a.P a.Q a.N V) 0 R₂ ∧
    Spec.Rsa.bytesAt t.mem (g.buffer 2).base (g.buffer 2).len = encode g (maskOf a.P a.Q a.N V) 1 R₃ ∧
    Spec.Rsa.bytesAt t.mem (g.buffer 4).base (g.buffer 4).len = encode g (maskOf a.P a.Q a.N V) 2 X ∧
    t.gpr .eax = BitVec.ofNat 32 (maskOf a.P a.Q a.N V).toNat

theorem sized_ok [VG.Proof.Rsa.X86.BatchLaw] {g : CallGeometry} {s : State} (h : Inputs g s) (len : Lengths g) :
    WP isa sized s fun t => Inputs g t ∧ ArithmeticPost g s.mem t ∧
      Frame (bodyWrites g ++ [below (s.gpr .esp) 52]) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have nw := h.ws.workspace.nowrap
  unfold sized
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (loads_ok h len) fun u ⟨hu, start, ou, ru⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  obtain ru' := inputsRt hu len
  obtain lens : (g.args 9).toNat ≤ 1024 ∧ (g.args 11).toNat ≤ 1024 := by
    obtain b1 : (g.args 9).toNat ≤ 8 * g.n := hu.inputBound 1
    obtain b2 : (g.args 11).toNat ≤ 8 * g.n := hu.inputBound 2
    have up := hu.upper
    omega_using [b1, b2, up]
  refine WP.mono (core_ok start (inputsGate hu s.mem) lens fun t K O => (hu.afterBelow K (by decide) (by decide)
      (VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS.toFrame
        (fun _ _ o => scratchFrame hu (keep_outside ru'.ws o (by decide) (by decide))) O)).arguments 9 (by decide))
    fun v ⟨kv, rv, zero, computed⟩ => ?_
  obtain kwEq : kw (g.args 7).toNat = 2 * g.n := by rw [len.width]
  obtain spU : u.gpr .esp = s.gpr .esp := ru.1 .esp (by decide)
  rw [spU] at kv
  have fv : Frame (g.writes ++ [below (s.gpr .esp) 52]) u.mem v.mem :=
    VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS.toFrame
      (fun _ _ o => scratchFrame hu (keep_outside ru'.ws o (by decide) (by decide))) kv
  obtain bv : Frame ([⟨off g.base 16, g.size - 16⟩] ++ [below (s.gpr .esp) 52]) u.mem v.mem :=
    VG.Proof.RsaKeyGen.X86.KeyRuntime.OutsS.toFrame (fun _ _ o => outside_frame
      (hu.keepBody (by rw [← kwEq]; exact o) (by decide) (by decide)) (by omega_using [nw])) kv
  obtain hv := hu.afterBelow rv (by decide) (by decide) (by rw [spU]; exact fv)
  obtain ⟨V, mask, inverse⟩ := computed.mask
  refine WP.mono (stores_ok hv len zero _ mask) fun t ⟨ht, dp, dq, qi, status, frame, rest⟩ => ?_
  refine ⟨ht, ?_, ?_, ru.trans ((rv.mono (by decide)).trans rest)⟩
  · exact ⟨V, _, _, _, inverse, computed.remP, computed.remQ, dp, dq, qi, status⟩
  · have prior := outside_frame ou (by omega_using [nw])
    exact ((prior.mono (rs' := bodyWrites g ++ [below (s.gpr .esp) 52]) (by simp [bodyWrites])).trans
      (bv.mono (by simp [bodyWrites]))).trans (frame.mono (by simp [bodyWrites]))

end VG.Proof.Rsa.X86.CrtValuesRt
