import VerifiedGarbage.Proof.Bignum.X86_64.AdxSquareGroupedMemory

/-! Load, compute and store one pair inside a grouped diagonal. -/
namespace VG.Proof.Bignum.X86_64.AdxSquareGrouped
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64 (Keep)

def CoreResult (carry : Nat) (s t : State) : Prop := ∃ c o : Bool,
  t.cf = some c ∧ t.of = some o ∧ t.gpr .rsi = 0 ∧
  (t.gpr .r11).toNat + 2 ^ 64 * (t.gpr .r12).toNat + 2 ^ 128 * (c.toNat + o.toNat) =
    2 * ((s.gpr .r11).toNat + 2 ^ 64 * (s.gpr .r12).toNat) +
      (s.gpr .rdx).toNat * (s.gpr .rdx).toNat + carry ∧
  Keeps [.rax, .rcx, .rsi, .r11, .r12] s t

def stepRegs : List Reg := [.rdx, .r11, .r12, .rax, .rcx, .rsi]

theorem step_ok {s : State} {B : Addr} {Z A eb i k carry : Nat} (core : List Instr)
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 i) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2*i))
    (hA : A + 16*(i+k) + 16 ≤ Z) (hb : eb + 8*(i+k) + 8 ≤ Z)
    (hc : ∀ a, Keeps [.rdx, .r11, .r12] s a → a.cf = s.cf → a.of = s.of →
      WP isa (.block core) a (CoreResult carry a)) :
    WP isa (AdxSquareGrouped.step k core) s fun t => ∃ c o : Bool,
      t.cf = some c ∧ t.of = some o ∧ t.gpr .rsi = 0 ∧
      wv t.mem B (A + 16*(i+k)) 2 + 2 ^ 128 * (c.toNat + o.toNat) =
        2 * wv s.mem B (A + 16*(i+k)) 2 +
          (word s.mem B (eb + 8*(i+k))).toNat * (word s.mem B (eb + 8*(i+k))).toNat + carry ∧
      Outside B (A + 16*(i+k)) 16 s.mem t.mem ∧ Keep stepRegs s t := by
  unfold AdxSquareGrouped.step
  refine WP.seq (WP.mono (head_ok hs h8 h9 hbp h14 hA hb)
    fun a ⟨hdx, h11, h12, cfa, ofa, ka⟩ => ?_)
  refine WP.seq (WP.mono (hc a ka cfa ofa) fun b ⟨cb, ob, hcb, hob, zb, eb', kb⟩ => ?_)
  have kab := ka.trans kb
  refine WP.mono (store_ok (hs.congr kab.2.2.2) ((kab.gpr (by decide)).trans h8)
    ((kab.gpr (by decide)).trans h14) hA) fun t ⟨hm, hct, hot, kt⟩ => ?_
  obtain ⟨hv, hout⟩ := AdxSquare.write2 b.mem B (A + 16*(i+k)) (b.gpr .r11) (b.gpr .r12)
    (by have := hs.nowrap; omega)
  rw [← hm] at hv hout
  rw [kab.2.1] at hout
  refine ⟨cb, ob, hct.trans hcb, hot.trans hob, (kt.gpr (by simp)).trans zb, ?_, hout,
    (kab.keep.trans kt).mono (by decide)⟩
  rw [hv, AdxSquare.wv2]
  rw [h11, h12, hdx] at eb'
  exact eb'

theorem initialStep_ok {s : State} {B : Addr} {Z A eb i k : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 i) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2*i))
    (hA : A + 16*(i+k) + 16 ≤ Z) (hb : eb + 8*(i+k) + 8 ≤ Z)
    (hc : (s.gpr .r15).toNat ≤ 2) :
    WP isa (AdxSquareGrouped.step k AdxSquareGrouped.initialPair) s fun t => ∃ c o : Bool,
      t.cf = some c ∧ t.of = some o ∧ t.gpr .rsi = 0 ∧
      wv t.mem B (A + 16*(i+k)) 2 + 2 ^ 128 * (c.toNat + o.toNat) =
        2 * wv s.mem B (A + 16*(i+k)) 2 +
          (word s.mem B (eb + 8*(i+k))).toNat * (word s.mem B (eb + 8*(i+k))).toNat +
            (s.gpr .r15).toNat ∧
      Outside B (A + 16*(i+k)) 16 s.mem t.mem ∧ Keep stepRegs s t := by
  apply step_ok _ hs h8 h9 hbp h14 hA hb
  intro a ka _ _
  have ha : a.gpr .r15 = s.gpr .r15 := ka.gpr (by decide)
  unfold CoreResult
  simpa only [ha] using initialPair_ok a (by simpa only [ha] using hc)

theorem nextStep_ok {s : State} {B : Addr} {Z A eb i k : Nat} {c o : Bool}
    (hs : Scr s B Z) (h8 : s.gpr .r8 = off B A) (h9 : s.gpr .r9 = off B eb)
    (hbp : s.gpr .rbp = BitVec.ofNat 64 i) (h14 : s.gpr .r14 = BitVec.ofNat 64 (2*i))
    (hA : A + 16*(i+k) + 16 ≤ Z) (hb : eb + 8*(i+k) + 8 ≤ Z)
    (hc : s.cf = some c) (ho : s.of = some o) (hz : s.gpr .rsi = 0) :
    WP isa (AdxSquareGrouped.step k AdxSquareGrouped.pair) s fun t => ∃ c' o' : Bool,
      t.cf = some c' ∧ t.of = some o' ∧ t.gpr .rsi = 0 ∧
      wv t.mem B (A + 16*(i+k)) 2 + 2 ^ 128 * (c'.toNat + o'.toNat) =
        2 * wv s.mem B (A + 16*(i+k)) 2 +
          (word s.mem B (eb + 8*(i+k))).toNat * (word s.mem B (eb + 8*(i+k))).toNat +
            c.toNat + o.toNat ∧
      Outside B (A + 16*(i+k)) 16 s.mem t.mem ∧ Keep stepRegs s t := by
  have base := step_ok (carry := c.toNat + o.toNat) AdxSquareGrouped.pair hs h8 h9 hbp h14 hA hb
  apply WP.mono (base ?_)
  · intro t ⟨ct, ot, hct, hot, zt, et, hout, kt⟩
    exact ⟨ct,ot,hct,hot,zt,by omega,hout,kt⟩
  · intro a ka hca hoa
    refine WP.mono (pair_ok a (hca.trans hc) (hoa.trans ho)) fun t ⟨ct,ot,hct,hot,et,kt⟩ => ?_
    refine ⟨ct,ot,hct,hot,?_,by omega,kt.mono (by decide)⟩
    exact (kt.gpr (by decide)).trans ((ka.gpr (by decide)).trans hz)

end VG.Proof.Bignum.X86_64.AdxSquareGrouped
