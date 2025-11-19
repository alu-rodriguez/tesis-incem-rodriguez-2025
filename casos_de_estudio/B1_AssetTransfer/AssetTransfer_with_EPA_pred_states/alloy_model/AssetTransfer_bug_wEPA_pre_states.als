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
	pre_constructor[e]
}
