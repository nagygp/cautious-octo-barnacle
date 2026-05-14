# Conjectures Duales Topologiques — Formalisation CIC

## Symboles Unicode du Calcul des Constructions Inductives

### Résultats Connus (■ = black-boxé, `sorry` en Lean)

```
■₁  ∀ (S : Spec(α)) (c : ℝ), c > 0 → IsBent(S, c) → (∃ v, S(v) ≠ 0) → div(S) = 1
■₂  ∀ (S : Spec(α)), (∃ v, S(v) ≠ 0) → div(S) ≥ 1
■₃  ∀ (S : Spec(α)), div(S) ≥ 2 → ∀ c > 0, ¬ IsBent(S, c)
■₄  ∀ (S : Spec(α)) (C : Cover(α)), div(S) ≤ Σᵢ div_local(S, Cᵢ)
■₅  ∀ (S : Spec(α)), H(S) ≥ 0
■₆  ∀ (S : Spec(α)), H(S) ≤ log|α|
■₇  ∀ (S : Spec(α)), IsBent(S, c) → H(S) = log(supp(S))
■₈  ∀ (S : Spec(α)), IsBent(S, c) → ‖S‖² = supp(S) · c²
```

---

### Axe 1 — Rigidité vs Cohomologie (Indice de Déformation)

**Définition** (Indice de Déformation Cohomologique) :
```
δ : Spec(α) → ℝ
δ(S) := 1 − 1/div(S)
```

**Corollaire 1.1** (δ = 0 ⟺ Bent) :
```
⊢ ∀ S c, c > 0 → IsBent(S,c) → (∃ v, S(v) ≠ 0) → δ(S) = 0
Preuve : δ(S) = 1 − 1/div(S) = 1 − 1/1 = 0    [par ■₁]
```

**Corollaire 1.2** (δ > 0 + non trivial ⟹ ¬Bent) :
```
⊢ ∀ S, δ(S) > 0 → (∃ v, S(v) ≠ 0) → ∀ c > 0, ¬ IsBent(S,c)
Preuve : Par contraposition de 1.1
```

**Corollaire 1.3** (δ ∈ [0, 1)) :
```
⊢ ∀ S, (∃ v, S(v) ≠ 0) → 0 ≤ δ(S) ∧ δ(S) < 1
Preuve : div(S) ≥ 1 [par ■₂] ⟹ 1/div(S) ∈ (0, 1] ⟹ δ ∈ [0, 1)
```

**Corollaire 1.4** (Monotonie) :
```
⊢ ∀ S₁ S₂, div(S₁) ≤ div(S₂) → div(S₁) > 0 → δ(S₁) ≤ δ(S₂)
Preuve : 1/div est décroissante ⟹ −1/div est croissante
```

---

### Axe 2 — Topos de Faisceaux (Cohérence Locale)

**Définition** (Diversité Locale) :
```
div_local : Spec(α) → Cover(α) → Fin(k) → ℕ
div_local(S, C, b) := |{ S(v) : v ∈ Cᵦ, S(v) ≠ 0 }|
```

**Corollaire 2.1** (Condition Faisceautique) :
```
⊢ ∀ S C, (∀ b, div_local(S,C,b) ≤ 1) → div(S) ≤ #blocs(C)
Preuve : div(S) ≤ Σᵢ div_local(S,Cᵢ) [par ■₄] ≤ Σᵢ 1 = #blocs
```

**Corollaire 2.2** (Bent Global ⟹ Bent Local) :
```
⊢ ∀ S c C, IsBent(S,c) → ∀ b, div_local(S,C,b) ≤ 1
Preuve : Chaque valeur locale est 0 ou c ⟹ au plus 1 valeur distincte non nulle
```

---

### Axe 3 — Flexibilité Spectrale (Entropie)

**Définition** (Entropie Normalisée) :
```
η : Spec(α) → [0, 1]
η(S) := H(S) / log|α|
```

**Corollaire 3.1** (η ∈ [0, 1]) :
```
⊢ ∀ S, |α| > 1 → 0 ≤ η(S) ≤ 1
Preuve : 0 ≤ H(S) [par ■₅] et H(S) ≤ log|α| [par ■₆]
```

**Corollaire 3.2** (Bent ⟹ η = log(m)/log(N)) :
```
⊢ ∀ S c, IsBent(S,c) → η(S) = log(supp(S))/log|α|
Preuve : H(S) = log(supp(S)) [par ■₇] ⟹ η = log(m)/log(N)
```

---

### Axe 4 — Topologie Temporelle

**Corollaire 4.1** (Stabilité par Combinaison) :
```
⊢ ∀ S₁ S₂ symétriques, ∀ a b : ℝ, a·S₁ + b·S₂ est symétrique
Preuve : S(k) = S(−k) ⟹ a·S₁(k) + b·S₂(k) = a·S₁(−k) + b·S₂(−k)
```

**Corollaire 4.2** (DC/Total Constant) :
```
⊢ ∀ traj, DC(t) = DC(0) → Total(t) = Total(0) → DC(t)/Total(t) = DC(0)/Total(0)
```

---

### Conjectures Croisées

**Corollaire 5.1** (‖R‖² ≤ ‖S‖²) :
```
⊢ ∀ D : Décomp, ‖D.rigid‖² ≤ ‖D.ambient‖²
Preuve : S(v) = R(v) + N(v) avec R,N ≥ 0 ⟹ R(v)² ≤ S(v)² par nlinarith
```

**Corollaire 5.3** (Rigide ⟹ δ = 0) :
```
⊢ ∀ D, (∃ v, D.rigid(v) ≠ 0) → δ(D.rigid) = 0
Preuve : D.rigid est bent [par construction] ⟹ div = 1 [par ■₁]
```

**Trichotomie Spectrale** :
```
∀ S, classif(S) ∈ { Cristallin, Fluide, Stochastique }
  Cristallin  : div(S) ≤ 1    (δ = 0, silence homotopique)
  Fluide      : 1 < div(S) < supp(S)  (0 < δ < 1)
  Stochastique: div(S) = supp(S) (δ → 1, bruit maximal)
```

---

### Application aux Données `event_spectrum.txt`

| Invariant                    | Valeur observée | Interprétation          |
|------------------------------|-----------------|-------------------------|
| N                            | 1024 = 2¹⁰     | Spectre sur ℤ/1024ℤ    |
| Diversité (dist. non nulles) | 885             | ≫ 1 → **non-bent**     |
| δ (déformation)              | 1 − 1/885 ≈ 0.9989 | État **fluide**     |
| η (entropie normalisée)      | 0.9576          | Proche du maximum       |
| Fraction DC (puissance)      | 66.3%           | DC dominant             |
| CV AC                        | 0.5956          | Modérément dispersé     |
| Paires exactes               | 139 (incl. 2^k)| Squelette dyadique      |
| Max |S(i)−S(N−i)|            | < 2×10⁻⁹       | Symétrie parfaite       |
| État spectral                | **Fluide**      | 1 < 885 < 1024         |

### Motif Dyadique Remarquable

Toutes les puissances de 2 dans {4, 8, 16, 32, 64, 128, 256} sont parmi
les 139 indices i tels que S(i) = S(N−i) exactement en virgule flottante.
Ce « squelette dyadique » est un invariant structurel du signal,
compatible avec la théorie des faisceaux sur un espace dyadique.
