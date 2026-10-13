#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_STATIONS 10
#define MAX_EVENTS 500000
#define GUARD 0.000001
#define MAX_BACKOFF_POWER 16

/* event types */
enum {
    TX_END,
    TX_START,
    ARRIVAL
};

/* simulation modes */
enum {
    FIXED,
    BINARY,
    PERSISTENT,
    SLOTTED
};

typedef struct Packet {
    double arrival;
    double service;
    double finish;
    int station;
    int collisions;
    int collided;
    struct Packet *next;
} Packet;

typedef struct {
    Packet *head;
    Packet *tail;
    long completed;
    long delay_count;
    double delay_sum;
} Station;

typedef struct {
    double time;
    unsigned long serial;
    int type;
    Packet *packet;
} Event;

typedef struct {
    int part;
    const char *protocol;
    int n;
    double rate;
    double backoff;
    double ratio;
    unsigned seed;
    int quick;
} Config;

static Event events[MAX_EVENTS];
static int event_count;
static unsigned long event_serial;

static uint64_t random_state;

static Station stations[MAX_STATIONS];
static Packet *air[MAX_STATIONS];

static int air_count;
static int nstations;

static long arrivals;
static long completed;
static long attempts;
static long failed_attempts;
static long delay_count;

static long backlog_begin;
static long backlog_end;

static double sum_delay;
static double warmup;
static double finish_time;


// generate random bits
static uint64_t random_bits(void)
{
    random_state ^= random_state >> 12;
    random_state ^= random_state << 25;
    random_state ^= random_state >> 27;

    return random_state *
           UINT64_C(2685821657736338717);
}


// uniform random number
static double uniform_random(void)
{
    return (random_bits() >> 11) * 0x1.0p-53;
}


// exponential random number
static double exponential_random(double mean)
{
    double u = uniform_random();

    return -mean * log(
        u > 0.0 ? u : 0x1.0p-53
    );
}


// compare two events
static int event_before(Event a, Event b)
{
    if (a.time != b.time) {
        return a.time < b.time;
    }

    if (a.type != b.type) {
        return a.type < b.type;
    }

    return a.serial < b.serial;
}


// add event to priority queue
static void push_event(
    double at,
    int type,
    Packet *packet
)
{
    if (event_count + 1 >= MAX_EVENTS) {
        fprintf(
            stderr,
            "event queue exceeded capacity\n"
        );

        exit(EXIT_FAILURE);
    }

    Event x = {
        at,
        ++event_serial,
        type,
        packet
    };

    int i = ++event_count;

    while (
        i > 1 &&
        event_before(x, events[i / 2])
    ) {
        events[i] = events[i / 2];
        i /= 2;
    }

    events[i] = x;
}


// remove next event
static Event pop_event(void)
{
    Event result = events[1];
    Event last = events[event_count--];

    int i = 1;

    while (i * 2 <= event_count) {
        int child = i * 2;

        if (
            child < event_count &&
            event_before(
                events[child + 1],
                events[child]
            )
        ) {
            child++;
        }

        if (!event_before(events[child], last)) {
            break;
        }

        events[i] = events[child];
        i = child;
    }

    if (event_count) {
        events[i] = last;
    }

    return result;
}


// add packet to station fifo
static void enqueue(
    Station *station,
    Packet *packet
)
{
    packet->next = NULL;

    if (station->tail) {
        station->tail->next = packet;
    } else {
        station->head = packet;
    }

    station->tail = packet;
}


// remove packet from station fifo
static Packet *take_front(Station *station)
{
    Packet *packet = station->head;

    station->head = packet->next;

    if (!station->head) {
        station->tail = NULL;
    }

    packet->next = NULL;

    return packet;
}


// reset values for next simulation
static void reset(
    unsigned seed,
    int n,
    int quick
)
{
    memset(stations, 0, sizeof(stations));

    nstations = n;

    event_count = 0;
    event_serial = 0;
    air_count = 0;

    arrivals = 0;
    completed = 0;
    attempts = 0;
    failed_attempts = 0;
    delay_count = 0;

    backlog_begin = 0;
    backlog_end = 0;

    sum_delay = 0.0;

    // shorter measurement for quick tests
    warmup = quick ? 250.0 : 3000.0;
    finish_time = quick ? 1250.0 : 23000.0;

    random_state =
        (uint64_t)seed +
        UINT64_C(0x9e3779b97f4a7c15);
}


// record completed packet statistics
static void record_completion(
    Packet *packet,
    double when
)
{
    Station *station = &stations[packet->station];

    if (when >= warmup && when <= finish_time) {

        completed++;
        station->completed++;

        if (packet->arrival >= warmup) {
            double delay = when - packet->arrival;

            sum_delay += delay;
            delay_count++;

            station->delay_sum += delay;
            station->delay_count++;
        }
    }
}


// find the next slot boundary
static double next_slot(double at)
{
    return ceil(at - 1e-10) + GUARD;
}


// calculate retransmission wait
static double retransmission_wait(
    Packet *packet,
    int mode,
    double fixed_backoff
)
{
    // parts 1 and 2
    if (mode == FIXED) {
        return exponential_random(fixed_backoff);
    }

    // part 4: station 0 is persistent
    if (
        mode == PERSISTENT &&
        packet->station == 0
    ) {
        return 0.0;
    }

    // part 3: binary exponential backoff
    int power = packet->collisions;

    if (power > MAX_BACKOFF_POWER) {
        power = MAX_BACKOFF_POWER;
    }

    double window = (double)(1u << power);

    // part 5 uses whole slots
    if (mode == SLOTTED) {
        return floor(uniform_random() * window);
    }

    return uniform_random() * window;
}


// start a packet transmission
static void start_transmission(
    Packet *packet,
    int mode,
    double when
)
{
    // overlapping transmissions collide
    for (int i = 0; i < air_count; i++) {
        air[i]->collided = 1;
        packet->collided = 1;
    }

    if (air_count >= MAX_STATIONS) {
        fprintf(
            stderr,
            "more transmissions than stations\n"
        );

        exit(EXIT_FAILURE);
    }

    air[air_count++] = packet;

    double duration =
        mode == SLOTTED
        ? 1.0 - 2.0 * GUARD
        : packet->service;

    push_event(
        when + duration,
        TX_END,
        packet
    );

    if (when >= warmup) {
        attempts++;
    }
}


// finish a packet transmission
static int finish_transmission(
    Packet *packet,
    int mode,
    double fixed_backoff,
    double when
)
{
    int found = 0;

    // remove packet from active transmissions
    for (int i = 0; i < air_count; i++) {

        if (air[i] == packet) {
            air[i] = air[--air_count];
            found = 1;
            break;
        }
    }

    if (!found) {
        fprintf(
            stderr,
            "packet missing from active transmissions\n"
        );

        exit(EXIT_FAILURE);
    }

    // collision occurred
    if (packet->collided) {

        if (when >= warmup) {
            failed_attempts++;
        }

        packet->collided = 0;
        packet->collisions++;

        double wait = retransmission_wait(
            packet,
            mode,
            fixed_backoff
        );

        double start = when + wait;

        // slotted aloha retransmission
        if (mode == SLOTTED) {
            start = next_slot(start);
        }

        // persistent station retransmission
        if (
            mode == PERSISTENT &&
            packet->station == 0
        ) {
            start = ceil(when - 1e-10);
        }

        push_event(
            start,
            TX_START,
            packet
        );

        return 0;
    }

    // successful transmission
    else {

        Station *station =
            &stations[packet->station];

        record_completion(packet, when);

        Packet *sent = take_front(station);

        if (sent != packet) {
            fprintf(
                stderr,
                "station fifo order violated\n"
            );

            exit(EXIT_FAILURE);
        }

        free(sent);

        // send next packet if queue is not empty
        if (station->head) {

            double start =
                mode == SLOTTED
                ? next_slot(when)
                : when;

            push_event(
                start,
                TX_START,
                station->head
            );
        }

        return 1;
    }
}


// write simulation results to csv
static void write_csv(FILE *file, Config cfg)
{
    double period = finish_time - warmup;

    long growth = backlog_end - backlog_begin;
    long sampled_arrivals = arrivals;

    // flag substantial queue buildup
    int overloaded =
        growth > 100 &&
        growth > sampled_arrivals / 20;

    double throughput = completed / period;

    double delay =
        delay_count
        ? sum_delay / delay_count
        : NAN;

    double work = attempts * (
        cfg.part == 6
        ? 1.0 / cfg.ratio
        : 1.0
    );

    double g = work / period;

    Station *first = &stations[0];

    long others = 0;
    long others_delay_count = 0;

    double others_delay = 0.0;

    // combine statistics for other stations
    for (int i = 1; i < nstations; i++) {

        others += stations[i].completed;

        others_delay_count +=
            stations[i].delay_count;

        others_delay += stations[i].delay_sum;
    }

    fprintf(
        file,
        "%d,%s,%d,%.8g,%.8g,%.8g,%u,"
        "%.8g,%.8g,%.8g,%.8g,"
        "%ld,%ld,%ld,%ld,%ld,"
        "%ld,%ld,%ld,%d,"
        "%.8g,%.8g,%.8g,%.8g,%.8g\n",

        cfg.part,
        cfg.protocol,
        cfg.n,
        cfg.rate,
        cfg.backoff,
        cfg.ratio,
        cfg.seed,

        warmup,
        finish_time,
        throughput,
        delay,

        attempts,
        failed_attempts,
        completed,
        delay_count,
        arrivals,

        backlog_begin,
        backlog_end,
        growth,
        overloaded,

        g,

        first->completed / period,

        first->delay_count
        ? first->delay_sum / first->delay_count
        : NAN,

        others / period,

        others_delay_count
        ? others_delay / others_delay_count
        : NAN
    );
}


// free remaining station packets
static void clear_queues(void)
{
    for (int i = 0; i < nstations; i++) {

        while (stations[i].head) {
            free(take_front(&stations[i]));
        }
    }
}


/*
 * parts 1 and 2: fixed backoff
 * part 3: binary exponential backoff
 * part 4: persistent station
 * part 5: slotted aloha
 */

static void run_aloha(
    FILE *file,
    Config cfg,
    int mode
)
{
    reset(cfg.seed, cfg.n, cfg.quick);

    // schedule first packet arrival
    push_event(
        exponential_random(1.0 / cfg.rate),
        ARRIVAL,
        NULL
    );

    int measurement_started = 0;

    long system_arrivals = 0;
    long system_departures = 0;

    while (event_count) {

        Event event = pop_event();
        double now = event.time;

        if (now > finish_time) {
            break;
        }

        // start measurement after warmup
        if (
            !measurement_started &&
            now >= warmup
        ) {
            backlog_begin =
                system_arrivals - system_departures;

            measurement_started = 1;
        }

        // packet arrival
        if (event.type == ARRIVAL) {

            int id = (int)(
                uniform_random() * cfg.n
            );

            if (id >= cfg.n) {
                id = cfg.n - 1;
            }

            Packet *packet = calloc(
                1,
                sizeof(*packet)
            );

            if (!packet) {
                exit(EXIT_FAILURE);
            }

            packet->arrival = now;
            packet->service = 1.0;
            packet->station = id;

            enqueue(&stations[id], packet);

            system_arrivals++;

            if (now >= warmup) {
                arrivals++;
            }

            // only queue head can transmit
            if (stations[id].head == packet) {

                double start =
                    mode == SLOTTED
                    ? next_slot(now)
                    : now;

                push_event(
                    start,
                    TX_START,
                    packet
                );
            }

            // schedule next Poisson arrival
            push_event(
                now + exponential_random(
                    1.0 / cfg.rate
                ),
                ARRIVAL,
                NULL
            );
        }

        // transmission starts
        else if (event.type == TX_START) {

            start_transmission(
                event.packet,
                mode,
                now
            );
        }

        // transmission finishes
        else {

            system_departures +=
                finish_transmission(
                    event.packet,
                    mode,
                    cfg.backoff,
                    now
                );
        }
    }

    // count unfinished packets
    long remaining_packets = 0;

    for (int i = 0; i < nstations; i++) {

        for (
            Packet *p = stations[i].head;
            p;
            p = p->next
        ) {
            remaining_packets++;
        }
    }

    backlog_end = remaining_packets;

    write_csv(file, cfg);

    clear_queues();
}


/*
 * part 6
 * reservation minislots and a separate fcfs data channel
 */

// complete packets when data service actually finishes
static long finish_data_packets(
    Packet **head,
    Packet **tail,
    double until
)
{
    long finished = 0;

    while (
        *head &&
        (*head)->finish <= until
    ) {
        Packet *packet = *head;

        *head = packet->next;

        if (!*head) {
            *tail = NULL;
        }

        record_completion(
            packet,
            packet->finish
        );

        finished++;

        free(packet);
    }

    return finished;
}


// run packet reservation simulation
static void run_reservation(
    FILE *file,
    Config cfg
)
{
    reset(cfg.seed, cfg.n, cfg.quick);

    double xr = 1.0 / cfg.ratio;

    double arrival_time =
        exponential_random(1.0 / cfg.rate);

    double data_available = 0.0;

    Packet *data_head = NULL;
    Packet *data_tail = NULL;

    int backoff_slots[MAX_STATIONS] = {0};

    long system_arrivals = 0;
    long system_departures = 0;

    int measurement_started = 0;

    // process reservation minislots
    for (long slot = 0; ; slot++) {

        double now = (double)slot * xr;
        double end = now + xr;

        if (end > finish_time + 1e-10) {
            break;
        }

        // process data transmissions that have finished
        system_departures += finish_data_packets(
            &data_head,
            &data_tail,
            now
        );

        // mark beginning of measurement window
        if (
            !measurement_started &&
            now >= warmup - 1e-10
        ) {
            backlog_begin =
                system_arrivals - system_departures;

            measurement_started = 1;
        }

        // generate packet arrivals
        while (arrival_time <= now) {

            int id = (int)(
                uniform_random() * cfg.n
            );

            if (id >= cfg.n) {
                id = cfg.n - 1;
            }

            Packet *packet = calloc(
                1,
                sizeof(*packet)
            );

            if (!packet) {
                exit(EXIT_FAILURE);
            }

            packet->arrival = arrival_time;

            // data packet lengths are exponential
            packet->service =
                exponential_random(1.0);

            packet->station = id;

            enqueue(&stations[id], packet);

            system_arrivals++;

            if (arrival_time >= warmup) {
                arrivals++;
            }

            arrival_time +=
                exponential_random(
                    1.0 / cfg.rate
                );
        }

        int selected[MAX_STATIONS] = {0};

        int contender = -1;
        int number_contending = 0;

        // select stations attempting reservation
        for (int i = 0; i < cfg.n; i++) {

            if (!stations[i].head) {
                continue;
            }

            if (backoff_slots[i] > 0) {
                backoff_slots[i]--;
                continue;
            }

            selected[i] = 1;

            contender = i;
            number_contending++;
        }

        if (now >= warmup) {
            attempts += number_contending;
        }

        // reservation collision
        if (number_contending > 1) {

            if (now >= warmup) {
                failed_attempts +=
                    number_contending;
            }

            // binary backoff for collided stations
            for (int i = 0; i < cfg.n; i++) {

                if (!selected[i]) {
                    continue;
                }

                Packet *packet =
                    stations[i].head;

                packet->collisions++;

                int k = packet->collisions;

                if (k > MAX_BACKOFF_POWER) {
                    k = MAX_BACKOFF_POWER;
                }

                backoff_slots[i] = (int)(
                    uniform_random() * (1u << k)
                );
            }
        }

        // successful reservation
        else if (number_contending == 1) {

            Packet *packet = take_front(
                &stations[contender]
            );

            double data_start =
                data_available > end
                ? data_available
                : end;

            packet->finish =
                data_start + packet->service;

            data_available = packet->finish;

            // add packet to fcfs data channel
            packet->next = NULL;

            if (data_tail) {
                data_tail->next = packet;
            } else {
                data_head = packet;
            }

            data_tail = packet;

            backoff_slots[contender] = 0;
        }
    }

    // finish data packets within measurement horizon
    system_departures += finish_data_packets(
        &data_head,
        &data_tail,
        finish_time
    );

    backlog_end =
        system_arrivals - system_departures;

    write_csv(file, cfg);

    clear_queues();

    // free remaining data channel packets
    while (data_head) {

        Packet *packet = data_head;

        data_head = packet->next;

        free(packet);
    }
}


// fixed backoff experiment
static void run_fixed(
    FILE *file,
    int n,
    double rate,
    double b,
    unsigned seed,
    int quick
)
{
    Config cfg = {
        1,
        "fixed",
        n,
        rate,
        b,
        0.0,
        seed,
        quick
    };

    run_aloha(file, cfg, FIXED);
}


// binary, persistent and slotted experiments
static void run_variant(
    FILE *file,
    int part,
    int n,
    double rate,
    unsigned seed,
    int quick
)
{
    int mode =
        part == 3 ? BINARY :
        part == 4 ? PERSISTENT :
                    SLOTTED;

    const char *name =
        part == 3 ? "binary" :
        part == 4 ? "persistent" :
                    "slotted";

    Config cfg = {
        part,
        name,
        n,
        rate,
        0.0,
        0.0,
        seed,
        quick
    };

    run_aloha(file, cfg, mode);
}


// run all lab experiments
int main(int argc, char **argv)
{
    int quick =
        argc > 1 &&
        strcmp(argv[1], "--quick") == 0;

    FILE *file = fopen(
        "lab3_results.csv",
        "w"
    );

    if (!file) {
        perror("lab3_results.csv");
        return EXIT_FAILURE;
    }

    // csv column headings
    fprintf(
        file,
        "part,protocol,stations,lambda,backoff,"
        "x_over_xr,seed,warmup,end_time,"
        "throughput,mean_delay,attempts,"
        "failed_attempts,completed,delay_samples,"
        "arrivals,backlog_start,backlog_end,"
        "backlog_growth,unstable,aggregate_G,"
        "station0_throughput,station0_delay,"
        "others_throughput,others_delay\n"
    );

    // random generator seeds
    unsigned seeds[] = {
        400442107u,
        222222u,
        333333u
    };

    // arrival rates for parts 1 to 5
    double aloha_rates[] = {
        0.02, 0.05, 0.08, 0.10,
        0.12, 0.15, 0.18, 0.20,
        0.24, 0.28, 0.32, 0.36,
        0.42, 0.50
    };

    // arrival rates for reservation experiment
    double reservation_rates[] = {
        0.05, 0.10, 0.20, 0.35,
        0.50, 0.65, 0.75, 0.85,
        0.95, 1.05, 1.20, 1.40,
        1.60
    };

    // packet duration to reservation slot ratios
    double ratios[] = {
        1.0, 2.0, 3.0, 5.0,
        10.0, 20.0, 50.0
    };

    int seeds_count = quick ? 1 : 3;

    int aloha_count = quick
        ? 5
        : (int)(
            sizeof(aloha_rates) /
            sizeof(aloha_rates[0])
        );

    int reservation_count = quick
        ? 5
        : (int)(
            sizeof(reservation_rates) /
            sizeof(reservation_rates[0])
        );

    // parts 1 to 5
    for (int n = 5; n <= 10; n += 5) {

        double choices5[] = {
            3.0, 5.0, 7.0
        };

        double choices10[] = {
            5.0, 10.0, 20.0
        };

        // parts 1 and 2: fixed exponential backoff
        for (int k = 0; k < 3; k++) {

            double backoff =
                n == 5
                ? choices5[k]
                : choices10[k];

            for (int j = 0; j < aloha_count; j++) {

                for (int s = 0; s < seeds_count; s++) {

                    run_fixed(
                        file,
                        n,
                        aloha_rates[j],
                        backoff,
                        seeds[s],
                        quick
                    );
                }
            }
        }

        // parts 3, 4 and 5
        for (int j = 0; j < aloha_count; j++) {

            for (int s = 0; s < seeds_count; s++) {

                for (int part = 3; part <= 5; part++) {

                    run_variant(
                        file,
                        part,
                        n,
                        aloha_rates[j],
                        seeds[s],
                        quick
                    );
                }
            }
        }
    }

    // part 6: reservation system
    int ratio_count = (int)(
        sizeof(ratios) /
        sizeof(ratios[0])
    );

    for (int k = 0; k < ratio_count; k++) {

        for (int j = 0; j < reservation_count; j++) {

            for (int s = 0; s < seeds_count; s++) {

                Config cfg = {
                    6,
                    "reservation",
                    10,
                    reservation_rates[j],
                    0.0,
                    ratios[k],
                    seeds[s],
                    quick
                };

                run_reservation(file, cfg);
            }
        }
    }

    fclose(file);

    puts("Saved lab3_results.csv");

    return EXIT_SUCCESS;
}