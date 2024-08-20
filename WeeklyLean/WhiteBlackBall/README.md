# White and Black Balls

Consider the following game:
There is a bag of balls that has at least two balls to begin with. Each ball in the bag can be black or white. Each turn consists of removing two balls from the bag and placing a new ball. The player takes turns until there is only one ball left in the bag. The rules for each turn are:
- {White, White} -> {White} (If the player removes two white balls, they put a new white ball in the bag.)
- {White, Black} -> {Black}
- {Black, Black} -> {White}

## Challenge
**Prove that**:
1. If the bag begins with an even number of black balls, it ends with a white ball.
2. If the bag begins with an odd number of black balls, it ends with a black ball.
