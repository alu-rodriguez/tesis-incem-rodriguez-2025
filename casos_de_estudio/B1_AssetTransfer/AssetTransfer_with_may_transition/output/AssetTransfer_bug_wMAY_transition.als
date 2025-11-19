// AssetTransfer - Version BUGGY 2: Bug en makeOffer
// PROBLEMA: Al hacer oferta por mas que el precio original, se olvida asignar el tasador

// concrete states
abstract sig Address{}
one sig Address0x0 extends Address{}
one sig AddressNull extends Address{}
one sig AddressOwner extends Address{}
one sig AddressBuyer extends Address{}
one sig AddressAppraiser extends Address{}

abstract sig Bool{}
one sig True extends Bool{}
one sig False extends Bool{}

abstract sig EstadoContrato{}
one sig Active extends EstadoContrato{}
one sig OfferPlaced extends EstadoContrato{}
one sig Accepted extends EstadoContrato{}
one sig Terminated extends EstadoContrato{}


abstract sig EstadoConcreto {
	_instanceOwner: Address,
	_askingPrice: Int,
	_instanceBuyer: Address,
	_offerPrice: Int,
	_instanceAppraiser: Address,
	_state: EstadoContrato,
	_init: Bool
}


pred pre_constructor[ein:EstadoConcreto] {
	ein._init = False
	ein._instanceBuyer = Address0x0
	ein._offerPrice = 0
	ein._instanceAppraiser = Address0x0
}

pred pre_params_constructor[ein: EstadoConcreto, sender: Address, price: Int] {
	price >= 100
	sender != Address0x0
}

pred met_constructor[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address, price: Int] {
	//Pre
	pre_constructor[ein]
	pre_params_constructor[ein, sender, price]

	//Post
	eout._instanceOwner = sender
	eout._askingPrice = price
	eout._state = Active
	eout._init = True

	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
	eout._instanceAppraiser = ein._instanceAppraiser
}

pred invariante[e:EstadoConcreto] {
	e._init = True
	e._instanceOwner != Address0x0
	e._instanceOwner != e._instanceBuyer
	e._offerPrice >= 0
	e._askingPrice >= 100

	e._instanceBuyer = Address0x0 implies (e._state = Active or e._state = Terminated)
	e._state = Active implies (e._instanceBuyer = Address0x0)

	//(e._state = OfferPlaced) implies e._instanceAppraiser != Address0x0
}

pred pre_makeOffer[ein: EstadoConcreto] {
	ein._init = True
	ein._state = Active
  	ein._instanceBuyer = Address0x0   // asegura primera y única oferta
}

pred pre_params_makeOffer[ein: EstadoConcreto, sender: Address, appraiser: Address, offerPrice: Int] {
	sender != Address0x0
	sender != ein._instanceOwner
	appraiser != Address0x0
	offerPrice > 0
}

pred met_makeOffer[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address, 
		appraiser: Address, offerPrice: Int] {
	//Pre
	pre_makeOffer[ein]
	pre_params_makeOffer[ein, sender, appraiser, offerPrice]
	
	//Post
	eout._instanceBuyer = sender
	eout._offerPrice = offerPrice
	eout._state = OfferPlaced
	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._init = ein._init

	// BUG: Solo asigna appraiser si la oferta es MAYOR que el asking price
	(offerPrice > ein._askingPrice) implies eout._instanceAppraiser = appraiser
	(offerPrice <= ein._askingPrice) implies eout._instanceAppraiser = ein._instanceAppraiser // BUG: NO asigna appraiser
	
}

pred pre_terminate[ein: EstadoConcreto] {
	ein._init = True
	some ein._state
	ein._state != Terminated
	ein._state != Accepted
	ein._state = OfferPlaced implies ein._instanceAppraiser != Address0x0
}

pred pre_params_terminate[ein: EstadoConcreto, sender:Address] {
	sender != Address0x0
	ein._instanceOwner = sender
}

pred met_terminate[ein: EstadoConcreto, eout: EstadoConcreto, sender: Address] {
	//Pre
	pre_terminate[ein]
	pre_params_terminate[ein, sender]

	//Post
	eout._state = Terminated

	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
	eout._instanceAppraiser = ein._instanceAppraiser
	eout._init = ein._init
}

pred pre_accept[ein: EstadoConcreto] {
	ein._init = True
	ein._state = OfferPlaced
	ein._instanceBuyer != Address0x0
	ein._instanceAppraiser != Address0x0
}

pred pre_params_accept[ein: EstadoConcreto, sender: Address] {
	sender != Address0x0
	ein._instanceOwner = sender
}

pred met_accept[ein: EstadoConcreto, eout: EstadoConcreto, sender:Address] {
	//Pre
	pre_accept[ein]
	pre_params_accept[ein, sender]

	//Post
	eout._state = Accepted

	eout._instanceOwner = ein._instanceOwner
	eout._askingPrice = ein._askingPrice
	eout._instanceBuyer = ein._instanceBuyer
	eout._offerPrice = ein._offerPrice
	eout._instanceAppraiser = ein._instanceAppraiser
	eout._init = ein._init
}

pred pre_activated[ein: EstadoConcreto] {
  ein._init = True
  ein._state = Active
}

pred pre_offerPlaced[ein: EstadoConcreto] {
  ein._init = True
  ein._state = OfferPlaced
}

pred pre_offerAccepted[ein: EstadoConcreto] {
  ein._init = True
  ein._state = Accepted
}

pred pre_terminated[ein: EstadoConcreto] {
  ein._init = True
  ein._state = Terminated
}

// Initial partition for EPA=True: only the constructor precondition state
pred partitionS00[e: EstadoConcreto]{ // 
	e._init = False
}

pred partitionS01[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Active
}

pred partitionS02[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = OfferPlaced
}

pred partitionS03[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Accepted
}

pred partitionS04[e: EstadoConcreto]{ // 
	(invariante[e])
	e._state = Terminated 
}



//======predicates for blue queries======



pred blue_transition__S01__a__S04__mediante_met_terminate {
	some x: EstadoConcreto | partitionS01[x] and (not pre_terminate[x] or (all sender:{this/Address} | pre_params_terminate[x,sender] implies some y:EstadoConcreto | met_terminate[x,y,sender] and not partitionS04[y]))
}
run blue_transition__S01__a__S04__mediante_met_terminate for 8 EstadoConcreto, 8 Int, 5 Address

pred blue_transition__S00__a__S01__mediante_met_constructor {
	some x: EstadoConcreto | partitionS00[x] and ((all sender:{this/Address}, price:{Int} | pre_params_constructor[x,sender, price] implies some y:EstadoConcreto | met_constructor[x,y,sender, price] and not partitionS01[y]))
}
run blue_transition__S00__a__S01__mediante_met_constructor for 8 EstadoConcreto, 8 Int, 5 Address

pred blue_transition__S01__a__S02__mediante_met_makeOffer {
	some x: EstadoConcreto | partitionS01[x] and (not pre_makeOffer[x] or (all sender:{this/Address}, appraiser:{this/Address}, offerPrice:{Int} | pre_params_makeOffer[x,sender, appraiser, offerPrice] implies some y:EstadoConcreto | met_makeOffer[x,y,sender, appraiser, offerPrice] and not partitionS02[y]))
}
run blue_transition__S01__a__S02__mediante_met_makeOffer for 8 EstadoConcreto, 8 Int, 5 Address

pred blue_transition__S02__a__S03__mediante_met_accept {
	some x: EstadoConcreto | partitionS02[x] and (not pre_accept[x] or (all sender:{this/Address} | pre_params_accept[x,sender] implies some y:EstadoConcreto | met_accept[x,y,sender] and not partitionS03[y]))
}
run blue_transition__S02__a__S03__mediante_met_accept for 8 EstadoConcreto, 8 Int, 5 Address

pred blue_transition__S02__a__S04__mediante_met_terminate {
	some x: EstadoConcreto | partitionS02[x] and (not pre_terminate[x] or (all sender:{this/Address} | pre_params_terminate[x,sender] implies some y:EstadoConcreto | met_terminate[x,y,sender] and not partitionS04[y]))
}
run blue_transition__S02__a__S04__mediante_met_terminate for 8 EstadoConcreto, 8 Int, 5 Address




//======predicates for turquoise queries======



