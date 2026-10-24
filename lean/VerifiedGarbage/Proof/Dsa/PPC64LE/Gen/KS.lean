module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Pieces
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: steps in the key working space

The operations on the arrays of the key working space
(`Impl/Rsa/PPC64LE/KeyWs.lean`) are proven (`Proof/Rsa/PPC64LE/KeyOps.lean`,
…) on a state whose one writable region is the working space, with its
registers set (`Ws`). `SS.ksWP` runs such code from a state of the search,
narrowed to the working space (`SS.ws`, given the registers `KR`), and
`SS.of_ks` is the state after it: what the step wrote of the arrays and
header words, everything else as it was.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Rsa.KeyWorkspace
open VG.Proof.Rsa.PPC64LE.Keys (Ws)
open VG.Impl.Dsa.PPC64LE.Generation

/-- The state narrowed to the key working space. -/
abbrev GP.ksState (G : GP) (s : State) : State := s.withRegions s.rd [G.rK]

/-- The key working space's registers: its digits, its stride and its base. -/
structure KR (G : GP) (s : State) : Prop where
  r29 : s.gpr .r29 = BitVec.ofNat 64 G.w
  r30 : s.gpr .r30 = BitVec.ofNat 64 (S G.w)
  r31 : s.gpr .r31 = G.KB

theorem KR.of_keep {G : GP} {s t : State} {ws : List Reg} (h : KR G s) (k : Keep ws s t)
    (h29 : .r29 ∉ ws := by decide) (h30 : .r30 ∉ ws := by decide) (h31 : .r31 ∉ ws := by decide) : KR G t :=
  ⟨(k.gpr h29).trans h.r29, (k.gpr h30).trans h.r30, (k.gpr h31).trans h.r31⟩

section
variable {G : GP} {STK : Nat} {σ : State} {c : Cfg} {s : State}

theorem SS.kbNat (h : SS G STK σ c s) : G.KB.toNat = G.scr.toNat + kB G.pLen := by
  have := h.gi.wBig; have := h.gi.kBig; have := h.gi.scrFit
  have : 0 < kz G.pLen := by simp only [kz, hdr]; omega
  rw [GP.KB, GP.sa, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show kB G.pLen < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem SS.wsWith (h : SS G STK σ c s) (hr : KR G s) (rd : List Region) :
    Ws (s.withRegions rd [G.rK]) G.KB (kz G.pLen) G.w nArrs := by
  have := h.gi.wBig; have := h.gi.kBig; have := h.gi.scrFit
  have e := h.kbNat
  have l := h.lens
  refine ⟨VG.Proof.Bignum.PPC64LE.Scr.of_mem (List.mem_singleton_self _) (by show _ + kz G.pLen ≤ _; omega),
    ?_, ?_, ?_, hr.r29, hr.r30, hr.r31⟩ <;>
    simp only [arr, S, hdr, nArrs, kz, GP.w] <;> rcases l with e | e | e <;> rw [e] <;> decide

theorem SS.ws (h : SS G STK σ c s) (hr : KR G s) : Ws (G.ksState s) G.KB (kz G.pLen) G.w nArrs := h.wsWith hr s.rd

/-- The narrowed state's regions are within the state's. -/
theorem SS.kcov (h : SS G STK σ c s) : Covers (s.rd ++ [G.rK]) (s.rd ++ s.wr) ∧ Covers [G.rK] s.wr := by
  have inS : G.rScr ∈ s.wr := by rw [h.gi.wr, h.gi.pre.wr, h.gi.hG]; simp
  have big := h.gi.wBig; have kb := h.gi.kBig
  have hw : Covers [G.rK] s.wr := (Covers.of_sub (rs' := [G.rScr]) fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact ⟨G.rScr, List.mem_singleton_self _, kB G.pLen, rfl, by show kB G.pLen + kz G.pLen ≤ G.scrLen * 8; omega⟩).trans
    (Covers.of_mem fun r hr => by rw [List.mem_singleton] at hr; subst hr; exact inS)
  exact ⟨Covers.append (Covers.refl _) hw, hw⟩

/-- Code in the key working space alone, from a state of the search. -/
theorem SS.ksWP (h : SS G STK σ c s) {code : Prog isa} (hn : code.noCalls = true) {P : State → Prop}
    (hwp : WP isa code (G.ksState s) P) {Q : State → Prop}
    (k : ∀ t, P (G.ksState t) → t.rd = s.rd → t.wr = s.wr → Frame [G.rK] s.mem t.mem → Q t) :
    WP isa code s Q := by
  refine regionModel.wp_narrow (r := s.rd) (w := [G.rK]) hwp h.kcov.1 h.kcov.2
    (Code.noFrames_of_noCalls hn) (.inl hn) fun t s' _ hr hw' f p => ?_
  have hr' : s'.rd = s.rd := hr
  refine k s' ?_ hr' hw' f
  show P (s'.withRegions s'.rd _)
  rw [hr']; exact p

/-- After a step in the key working space: its arrays and header words. -/
theorem SS.of_ks (h : SS G STK σ c s) {t : State} {ws : List Reg} (r : Keep ws s t) (sp : t.sp = s.sp)
    (f : Frame [G.rK] s.mem t.mem) {A : Nat → Nat} {live : List Nat} {KV : Nat → Nat} {kls : List Nat}
    (ha : Arrs t.mem G.KB G.w A live) (hl : ∀ j ∈ live, j < nArrs)
    (hk : ∀ d ∈ kls, slot t.mem G.KB d = KV d) (hko : ∀ d ∈ kls, KlsOk d) (h28 : .r28 ∉ ws := by decide) :
    SS G STK σ { c with A := A, live := live, KV := KV, kls := kls } t := by
  have gi := h.gi
  have big := gi.wBig
  have kb := gi.kBig
  have hE : hEnd ≤ kB G.pLen := by rcases gi.lens3 with e | e | e <;> rw [e] <;> decide
  refine ⟨gi.of_scr r sp (o := kB G.pLen) (n := kz G.pLen) hE (by omega) (f.mono (by simp)) h28,
    h.sb.frame f (fun x hx r hr => ?_) (fun x hx => ?_), h.clOk, ha, hl, hk, hko⟩
  · rw [List.mem_singleton] at hr; subst hr
    have := h.clOk x hx
    exact (gi.kdisj this.2.1 this.2.2).symm
  · have := (h.clOk x hx).2.2; have := gi.scrFit; omega

/-- After an operation that writes the array `o` (to `v`) and no header word. -/
theorem SS.of_op (h : SS G STK σ c s) {t : State} {ws : List Reg} (r : Keep ws s t) (sp : t.sp = s.sp)
    (f : Frame [G.rK] s.mem t.mem) {o v : Nat} (ho : o < nArrs) (kp : Keep G.KB G.w [o] [] s.mem t.mem)
    (e : num t.mem G.KB G.w o = v) (h28 : .r28 ∉ ws := by decide) :
    SS G STK σ { c with A := VG.Proof.Rsa.KeyWorkspace.upd c.A o v, live := o :: c.live } t := by
  have l := h.lens
  refine h.of_ks r sp f (fun j hj => ?_) (fun j hj => ?_) (fun d hd => ?_) h.kslOk h28
  · by_cases hjo : j = o
    · subst hjo; rw [VG.Proof.Rsa.KeyWorkspace.upd_self]; exact e
    · rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ hjo, kp.num (by simpa using fun e => hjo e.symm) (by simp)
        (by have := arrs_fit l (h.liveOk j ((List.mem_cons.mp hj).resolve_left hjo)); have := kz_eq l
            show arr (G.pLen / 4) j + 4 * (G.pLen / 4 + 2) ≤ 2 ^ 64; omega)]
      exact h.arrs j ((List.mem_cons.mp hj).resolve_left hjo)
  · rcases List.mem_cons.mp hj with rfl | hj
    · exact ho
    · exact h.liveOk j hj
  · rw [kp.slot (h.kslOk d hd).1 (by simp)]; exact h.ksl d hd

/-- After an operation that writes the header word `d` (to `v`) and no array. -/
theorem SS.of_opS (h : SS G STK σ c s) {t : State} {ws : List Reg} (r : Keep ws s t) (sp : t.sp = s.sp)
    (f : Frame [G.rK] s.mem t.mem) {d v : Nat} (hd : KlsOk d) (kp : Keep G.KB G.w [] [d] s.mem t.mem)
    (e : slot t.mem G.KB d = v) (h28 : .r28 ∉ ws := by decide) :
    SS G STK σ { c with KV := VG.Proof.Rsa.KeyWorkspace.upd c.KV d v, kls := d :: c.kls } t := by
  have l := h.lens
  refine h.of_ks r sp f (fun j hj => ?_) h.liveOk (fun e' he => ?_) (fun e' he => ?_) h28
  · rw [kp.num (by simp) (by simpa using hd.1)
      (by have := arrs_fit l (h.liveOk j hj); have := kz_eq l
          show arr (G.pLen / 4) j + 4 * (G.pLen / 4 + 2) ≤ 2 ^ 64; omega)]
    exact h.arrs j hj
  · by_cases hed : e' = d
    · subst hed; rw [VG.Proof.Rsa.KeyWorkspace.upd_self]; exact e
    · rcases List.mem_cons.mp he with rfl | he
      · exact absurd rfl hed
      rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ hed, kp.slot (h.kslOk e' he).1 (by
        simp only [List.mem_singleton, forall_eq]
        have := h.kslOk e' he; have := hd; simp only [KlsOk] at *; omega)]
      exact h.ksl e' he
  · rcases List.mem_cons.mp he with rfl | he
    · exact hd
    · exact h.kslOk e' he

end

end VG.Proof.Dsa.PPC64LE.Gen
