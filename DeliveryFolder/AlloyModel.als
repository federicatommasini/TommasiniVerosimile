open util/integer

// as previously specified, to one farmer is associated only one farm
sig Farmer{
property: one Farm,
waterConsumption: one WaterConsumption,
status: one Status,
evaluatedBy: one PolicyMaker
}

// for simplicity reasons, the size is expressed as an Int representing the square meters, with the 
//hypothesis of rounding the non integer values
sig Farm{
location: one Address,
size: one Int,
owner: one Farmer,
}{size>0}

sig Address{
referredTo: one Farm
}

sig Product{
cultivatedBy: some Farmer
}

sig Suggestion{
uploadedBy: one Farmer,
visualizedBy: set Farmer
}

sig HelpRequest{
requestedBy: one Farmer,
answeredBy: one Farmer
}{!(requestedBy = answeredBy)}

sig DiscussionForum{
writers: some Farmer
}

sig Message{
receiver: one Farmer,
sender: one PolicyMaker
}

// for simplicity reasons,  the quantity is expressed as an Int representing the liter
//for sqaure meters, with the hypothesis of rounding the non integer values
sig WaterConsumption{
quantity: one Int,
causedBy: one Farmer,
analyzedBy: set PolicyMaker
}{quantity > 0}

enum Status{
GoodStatus,
NormalStatus,
BadStatus
}

sig PolicyMaker{
visualizedRankings: set Ranking
}

abstract sig Ranking{
relatedTo: one Product,
includes: set RankingPosition
}

sig ImprovementRanking extends Ranking{}

sig RankingPosition {
position: one Int,
relatedTo: one Ranking,
referredTo: one Farmer
}{position>0}

//if to a farmer is associated a water consumption, this water consumption has to be associated 
//only with the same farmer
fact singleFarmerWaterConsumptionAssociation{
	all w: WaterConsumption, f:Farmer | w.causedBy = f iff f.waterConsumption = w 
}

//if to a farmer is associated a farm, this farm has to be associated only with the same farmer
fact singleFarmerFarmAssociation{
	all farmer: Farmer, farm:Farm | farmer.property = farm iff farm.owner = farmer 
}

//if to a farm is associated an address, this address has to be associated only with the same farm
fact singleFarmerWaterConsumptionAssociation{
	all f: Farm, a:Address | a.referredTo = f iff f.location = a 
}

//A suggestion can be uploaded only by a farmer who has a good status
fact UploadedOnlyByGoodFarmers{
      all s:Suggestion, f: Farmer | s.uploadedBy=f
     implies f.status=GoodStatus
}

//A help request can be  answered only by a farmer who has a good status
fact AnsweredOnlyByGoodFarmers{
      all h:HelpRequest, f: Farmer | h.answeredBy=f
     implies f.status=GoodStatus
}

//every Improvement Ranking is linked to a different product
fact onlyoneImprovementRankingForProduct{
	no disj r1,r2: ImprovementRanking | (r1.relatedTo = r2.relatedTo)
}

//Each farmer has to be accociated only to one ranking position for each ranking in which he participates
fact onlyOneRankingPositionForAFarmerInARanking{
	all disj rp1,rp2: RankingPosition | rp1.relatedTo = rp2.relatedTo 
	implies rp1.referredTo != rp2.referredTo
}

// in this way it is assured that if a ranking position is related to a ranking, it appears also in the 
//set of RankingPosition associated to the Ranking
fact associationBetweenRankingAndRankingPosition{
	all rp:RankingPosition, r:Ranking | rp.relatedTo = r 
	implies rp in r.includes
}

// in this way it is assured that a ranking position appears in the set of only a ranking
fact noOverlappingRankingPosition{
	all rp: RankingPosition, disj r,r1: Ranking | rp.relatedTo = r 
	implies rp not in r1.includes
}

// in this way two RankingPositions related to the same ranking cannot have the same position number
fact consistentPositions{
	(all disj p1,p2: RankingPosition | (p1.relatedTo = p2.relatedTo) 
	implies p1.position != p2.position)
}
// in this way the number of elements in an improvement ranking related to a product is the same of the 
//number of farmers who cultivates that product.
fact consistentSizeOfImprovementRanking{ 
	(all p: Product, r:ImprovementRanking | r.relatedTo = p
	implies #r.includes = #p.cultivatedBy)
}

//in this way every ranking position related to a specific ranking (and then to a specific product) can be 
//associated only to a farmer who produces that product.
fact consistentLinkBetweenFarmerAndPosition{
	(all p: Product, r:ImprovementRanking, f: Farmer | (r.relatedTo = p and f in p.cultivatedBy) 
	implies f in r.includes.referredTo )
}

//in this way it is mandatory to associate an improvement ranking for each product
fact oneImprovementRankingForProduct{
	all p:Product | (let ir = {r:ImprovementRanking | r.relatedTo = p} | #ir = 1)
}

//in this way the value of a position related to an ImprovementRanking is smaller or equal to the number 
//of farmers who cultivates that product (for instance, if 10 farmers cultivate tomatoes, none of them
//can be in the 11th position in the respective ranking)
fact consistentPositionsUpperBoundImprovementRankings{
	all p: Product, rp:RankingPosition | rp.relatedTo.relatedTo = p
	implies rp.position<= #p.cultivatedBy
}


pred show{}

run show for 10 but exactly 4 Farmer, exactly 2 Product
