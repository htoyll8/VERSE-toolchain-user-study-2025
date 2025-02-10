export interface Goal {
    hypotheses: string[];
    goal: string;
}

interface ContextBefore {
    fg_goals: Goal[];
    bg_goals: Goal[];
    given_up_goals: Goal[];
    shelved_goals: Goal[];
}

export interface Command {
    tactic: string;
    context_before: ContextBefore;
}

interface ProofStatesDictEntry {
    tactic: string;
    fgGoals: Goal[];
    bgGoals: Goal[];
    givenUpGoals: Goal[];
    shelvedGoals: Goal[];
}

export interface ProofStatesDict {
    [key: number]: ProofStatesDictEntry;
}
