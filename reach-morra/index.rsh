'reach 0.1';

// create enum for first 5 fingers
//const [ isHand, ZERO, ONE, TWO, THREE, FOUR, FIVE ] = makeEnum(6);

// create enum for results
const [ isResult, NO_WINS, A_WINS, B_WINS, DRAW,  ] = makeEnum(4);

// 0 = none, 1 = B wins, 2 = draw , 3 = A wins
const winner = (handBatman, guessBatman, handRobin, guessRobin) => {
  const total = handBatman + handRobin;

  if ( guessBatman == total && guessRobin == total  ) {
      // draw
      return DRAW
  }  else if ( guessRobin == total) {
      // Robin wins
      return B_WINS
  }
  else if ( guessBatman == total ) { 
      // Batman wins
      return A_WINS
  } else {
    // else noone wins
      return NO_WINS
  }
 
}
  
assert(winner(1,2,1,3 ) == A_WINS);
assert(winner(5,10,5,8 ) == A_WINS);

assert(winner(3,6,4,7 ) == B_WINS);
assert(winner(1,5,3,4 ) == B_WINS);

assert(winner(0,0,0,0 ) == DRAW);
assert(winner(2,4,2,4 ) == DRAW);
assert(winner(5,10,5,10 ) == DRAW);

assert(winner(3,6,2,4 ) == NO_WINS);
assert(winner(0,3,1,5 ) == NO_WINS);

forall(UInt, handBatman =>
  forall(UInt, handRobin =>
    forall(UInt, guessBatman =>
      forall(UInt, guessRobin =>
    assert(isResult(winner(handBatman, guessBatman, handRobin , guessRobin)))
))));


// Setup common functions
const commonInteract = {
  ...hasRandom,
  reportResult: Fun([UInt], Null),
  reportHands: Fun([UInt, UInt, UInt, UInt], Null),
  informTimeout: Fun([], Null),
  getHand: Fun([], UInt),
  getGuess: Fun([], UInt),
};

const BatmanInterect = {
  ...commonInteract,
  wager: UInt, 
  deadline: UInt, 
}

const RobinInteract = {
  ...commonInteract,
  acceptWager: Fun([UInt], Null),
}


export const main = Reach.App(() => {
  const A = Participant('Batman',BatmanInterect );
  const B = Participant('Robin', RobinInteract );
  init();

  // Check for timeouts
  const informTimeout = () => {
    each([A, B], () => {
      interact.informTimeout();
    });
  };

  A.only(() => {
    const wager = declassify(interact.wager);
    const deadline = declassify(interact.deadline);
  });
  A.publish(wager, deadline)
    .pay(wager);
  commit();

  B.only(() => {
    interact.acceptWager(wager);
  });
  B.pay(wager)
    .timeout(relativeTime(deadline), () => closeTo(A, informTimeout));
  

  var result = DRAW;
   invariant( balance() == 2 * wager && isResult(result) );

   ///////////////// While DRAW or NO_WINS //////////////////////////////
   while ( result == DRAW || result == NO_WINS ) {
    commit();

  A.only(() => {
    const _handBatman = interact.getHand();
    const [_commitBatman1, _saltBatman1] = makeCommitment(interact, _handBatman);
    const commitBatman1 = declassify(_commitBatman1);

    const _guessBatman = interact.getGuess();
    const [_commitBatman2, _saltBatman2] = makeCommitment(interact, _guessBatman);
    const commitBatman2 = declassify(_commitBatman2);

  })
  

  A.publish(commitBatman1, commitBatman2)
      .timeout(relativeTime(deadline), () => closeTo(B, informTimeout));
    commit();

  // Robin must NOT know about Batman hand and guess
  unknowable(B, A(_handBatman,_guessBatman, _saltBatman1,_saltBatman2 ));
  
  // Get Robin  hand
  B.only(() => {
    const handRobin = declassify(interact.getHand());
    const guessRobin = declassify(interact.getGuess());
  });

  B.publish(handRobin, guessRobin)
    .timeout(relativeTime(deadline), () => closeTo(A, informTimeout));
  commit();

  A.only(() => {
    const saltBatman1 = declassify(_saltBatman1);
    const handBatman = declassify(_handBatman);
    const saltBatman2 = declassify(_saltBatman2);
    const guessBatman = declassify(_guessBatman);

  });

  A.publish(saltBatman1,saltBatman2, handBatman, guessBatman)
    .timeout(relativeTime(deadline), () => closeTo(B, informTimeout));
  checkCommitment(commitBatman1, saltBatman1, handBatman);
  checkCommitment(commitBatman2, saltBatman2, guessBatman);

  
  each([A, B], () => {
    interact.reportHands(handBatman, guessBatman, handRobin, guessRobin);
  });

  result = winner(handBatman, guessBatman, handRobin, guessRobin);
  continue;
}
// check to make sure no DRAW or NO_WINS
assert(result == A_WINS || result == B_WINS);

each([A, B], () => {
  interact.reportResult(result);
});

transfer(2 * wager).to(result == A_WINS ? A : B);
commit();

});
