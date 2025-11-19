pragma solidity >=0.4.25 <0.6.0;
/*
 * ===================== AUDITOR ANOTACIONES =====================
 * Estas anotaciones NO formaban parte del contrato original completo.
 * Se añaden únicamente para documentar cómo este subconjunto fue
 * abstraído a Alloy en la tesis (MAY/MUST). No implican intención
 * original del autor; son notas de mapeo.
 * - Estados reducidos a: Active, OfferPlaced, Accepted, Terminated
 * - Se preserva BUG: MakeOffer asigna appraiser solo si offerPrice > AskingPrice
 * - Se eliminan roles y fases intermedias (PendingInspection, etc.)
 * - No se modelan flujos de fondos ni otros efectos laterales.
 * ================================================================
 */
contract AssetTransferSimplified {
    enum StateType { Active, OfferPlaced, Accepted, Terminated }

    address public InstanceOwner;      // @audit maps to _instanceOwner
    address public InstanceBuyer;      // @audit _instanceBuyer
    address public InstanceAppraiser;  // @audit _instanceAppraiser
    uint public AskingPrice;           // @audit _askingPrice (>=100)
    uint public OfferPrice;            // @audit _offerPrice
    StateType public State;            // @audit _state

    // @audit Invariante conceptual (Alloy):
    //   owner != 0x0
    //   owner != buyer
    //   AskingPrice >= 100
    //   buyer == 0x0 => State in {Active, Terminated}
    //   State == Active => buyer == 0x0

    event Offered(address buyer, uint price, address maybeAppraiser, bool appraiserAssigned);
    event Accepted(address owner);
    event Terminated(address owner);

    constructor(uint price) public {
        require(price >= 100, "AskingPrice too low");
        InstanceOwner = msg.sender;
        AskingPrice = price;
        State = StateType.Active;
    }

    // @audit BUG: asigna appraiser solo si offerPrice > AskingPrice (igual que modelo Alloy)
    function MakeOffer(address appraiser, uint offerPrice) public {
        require(State == StateType.Active, "Not Active");
        require(InstanceBuyer == address(0), "Buyer already set");
        require(msg.sender != InstanceOwner, "Owner cannot buy");
        require(appraiser != address(0), "Appraiser required");
        require(offerPrice > 0, "Offer must be > 0");

        InstanceBuyer = msg.sender;
        OfferPrice = offerPrice;
        State = StateType.OfferPlaced;

        // @audit BUG branch: solo se asigna appraiser si la oferta supera AskingPrice
        if (offerPrice > AskingPrice) {
            InstanceAppraiser = appraiser;
        }

        emit Offered(msg.sender, offerPrice, InstanceAppraiser, InstanceAppraiser != address(0));
    }

    // @audit Accept -> Alloy met_accept (pre_accept exige appraiser != 0)
    function Accept() public {
        require(State == StateType.OfferPlaced, "Not OfferPlaced");
        require(InstanceBuyer != address(0), "No buyer");
        require(InstanceAppraiser != address(0), "Appraiser missing (bug path)");
        require(msg.sender == InstanceOwner, "Only owner");
        State = StateType.Accepted;
        emit Accepted(msg.sender);
    }

    // @audit Terminate -> Alloy met_terminate (bloquea Accepted / Terminated; OfferPlaced requiere appraiser)
    function Terminate() public {
        require(msg.sender == InstanceOwner, "Only owner");
        require(State != StateType.Terminated, "Already terminated");
        require(State != StateType.Accepted, "Already accepted");
        if (State == StateType.OfferPlaced) {
            require(InstanceAppraiser != address(0), "Cannot terminate buggy incomplete offer");
        }
        State = StateType.Terminated;
        emit Terminated(msg.sender);
    }
}