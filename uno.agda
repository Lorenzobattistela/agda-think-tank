module uno where 

open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Fin using (Fin; toℕ)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Maybe

data Color : Set where
  Red Green Blue Yellow : Color

-- define equality for colors
_colorEq_ : Color → Color → Bool
Red colorEq Red = true
Green colorEq Green = true
Blue colorEq Blue = true
Yellow colorEq Yellow = true
_ colorEq _ = false

Number : Set
Number = Fin 9

Card : Set
Card = Color × Number

Player : Set
Player = List Card

Deck : Set
Deck = List Card

record GameState : Set where
  field
    players : List Player
    currentPlayer : Fin (length players)
    deck : Deck
    topCard : Card

sameColor : Card → Card → Bool
sameColor (c₁ , _) (c₂ , _) = c₁ colorEq c₂

sameNumber : Card → Card → Bool
sameNumber (_ , n₁) (_ , n₂) = (toℕ n₁) ≡ᵇ (toℕ n₂) 

canPlay : Card → Card → Bool
canPlay card₁ card₂ = sameColor card₁ card₂ ∨ sameNumber card₁ card₂


data Move : Set where
  PlayCard : Card → Move

updateGameState : GameState → Move → Maybe GameState
updateGameState gs (PlayCard card) = 
  if canPlay card (topCard gs)
  then Just (record gs { 
    players = players gs,
    currentPlayer = (currentPlayer gs) ,
    discardPile = card ∷ discardPile gs,
    topCard = card
  })
  else Nothing







