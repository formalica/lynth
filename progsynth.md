lynth should be able to synthsize such programs by using advance techniques, tests are in Test/ProgSynth
like ~/synquid is doing, but it is simple one, rather than our, because we also need to prove correctness, you can look its codes
user may give spec via inductive types or via constrains created from various predicates
create few tests where function is defined via inductive proposition and we need to synthesize its computable or decidable alternative
place them into Test/ProgSynth

think how we can implement this, this procedure can be relateivelly independent and use advance data structures in his own or we may reuse some already implemented logic of other procedures of lynth

some function implementations require aux functions, so you can create it isnide main function as local aux function or can store in global env by adding some unqiue prefix

since I have little knowledge in this area, I can not properly review your spec I can only answer to your high level questions, I recomend to write some very big separate implementation spec with lot of details and code snippets, so implementation spec will be preserved accross various sessions and various agents. you can ask me high level questions and decisions to make and also describe advantages and disadavntes and your recommendation so I can decide what to do