# ============================================================
# AIRLINE PASSENGER SATISFACTION PROJECT
# STEPS 1 - 22
#
# Group allocation:
# Pulindu      -> Steps 1 - 10
# Ayendri /
# Nisalma      -> Steps 11 - 12
# Vidu         -> Steps 13 - 22
#
# IMPORTANT:
# This script now runs Steps 1 - 22 (Steps 13-22 added at the end).
# Steps 13 - 22 start after the Step 12 section.
#
# CHANGES FROM ORIGINAL CODE:
# 1. Train/test split added before learned imputation
# 2. Exact duplicates removed before the split
# 3. Service-rating 0 values treated as N/A
# 4. N/A indicator flags added
# 5. Arrival.Delay missing values regression-imputed
# 6. Log transformations added for skewed variables
# 7. Spearman correlation used instead of default Pearson
# 8. Effect sizes added
# 9. Two-proportion tests added
# 10. Welch/Wilcoxon robustness checks added
# 11. More complete ANOVA analysis added
# 12. Logistic model comparison / selection / regularisation /
#     cross-validation added
# ============================================================


# ============================================================
# LOAD LIBRARIES
# ============================================================

# NOTE: the "caret" package is NOT used any more. It was only needed for
# createDataPartition() and createFolds(), which are defined below in base R.
# This avoids the "no package called 'lava'" error completely.
required_packages <- c(
  "tidyverse", "ggplot2", "dplyr", "corrplot", "psych",
  "e1071", "car", "MASS", "glmnet", "pROC", "leaps"
)

options(repos = c(CRAN = "https://cloud.r-project.org"))

for (p in required_packages) {
  if (!requireNamespace(p, quietly = TRUE)) {
    message("Installing package: ", p)
    tryCatch(
      install.packages(p, dependencies = TRUE),
      error = function(e) message("Could not install ", p, ": ", conditionMessage(e))
    )
  }
}

# Check everything before going further
still_missing <- required_packages[
  !vapply(required_packages, requireNamespace, logical(1), quietly = TRUE)
]

if (length(still_missing) > 0) {
  stop(
    "These packages could not be installed or loaded: ",
    paste(still_missing, collapse = ", "),
    "\nTry: restart R (Session > Restart R), then run\n",
    "install.packages(c(\"", paste(still_missing, collapse = "\", \""), "\"))",
    call. = FALSE
  )
}

suppressPackageStartupMessages({
  library(tidyverse)
  library(ggplot2)
  library(dplyr)
  library(corrplot)
  library(psych)
  library(e1071)
  library(car)
  library(MASS)
  library(glmnet)
  library(pROC)
  library(leaps)
})

# MASS masks dplyr::select, so make select() always mean dplyr's version
select <- dplyr::select

# ------------------------------------------------------------
# Base-R replacements for caret::createDataPartition / createFolds
# (stratified by the outcome, same idea as caret)
# ------------------------------------------------------------

createDataPartition <- function(y, p = 0.8, list = FALSE) {
  y <- factor(y)
  idx <- unlist(lapply(split(seq_along(y), y), function(i) {
    i[sample.int(length(i), max(1, round(p * length(i))))]
  }), use.names = FALSE)
  sort(idx)
}

createFolds <- function(y, k = 5) {
  y <- factor(y)
  fold_id <- integer(length(y))
  for (i in split(seq_along(y), y)) {
    i <- i[sample.int(length(i))]
    fold_id[i] <- rep_len(sample.int(k), length(i))
  }
  out <- split(seq_along(y), fold_id)
  names(out) <- paste0("Fold", seq_along(out))
  out
}

cat("\nAll packages loaded successfully.\n")


# ============================================================
# GENERAL SETTINGS
# ============================================================

SEED <- 2026

N_FOLDS <- 5

# IMPORTANT:
# The dataset documentation should be checked to confirm that
# 0 in service ratings means "Not Applicable / Not Used".
ZERO_MEANS_NA <- TRUE

# Only create an N/A flag for service variables having at least
# this many zero values.
ZERO_FLAG_MIN <- 100

set.seed(SEED)


# ============================================================
# HELPER FUNCTIONS
# ============================================================


# ------------------------------------------------------------
# Print p-values neatly
# ------------------------------------------------------------

fmt_p <- function(p) {
  
  ifelse(
    p < 0.0001,
    "< 0.0001",
    sprintf("%.4f", p)
  )
  
}


# ------------------------------------------------------------
# Cramer's V
# Measures association strength between categorical variables
# ------------------------------------------------------------

cramers_v <- function(x, y) {
  
  tb <- table(
    x,
    y
  )
  
  chi <- suppressWarnings(
    chisq.test(
      tb,
      correct = FALSE
    )
  )
  
  sqrt(
    as.numeric(
      chi$statistic
    ) /
      (
        sum(tb) *
          (
            min(dim(tb)) - 1
          )
      )
  )
}


# ------------------------------------------------------------
# Cohen's d
# Effect size for difference between two means
# ------------------------------------------------------------

cohens_d <- function(
    x,
    g) {
  
  g <- droplevels(
    factor(g)
  )
  
  m <- tapply(
    x,
    g,
    mean,
    na.rm = TRUE
  )
  
  s <- tapply(
    x,
    g,
    sd,
    na.rm = TRUE
  )
  
  n <- tapply(
    x,
    g,
    function(z)
      sum(!is.na(z))
  )
  
  sp <- sqrt(
    (
      (n[1] - 1) * s[1]^2 +
        (n[2] - 1) * s[2]^2
    ) /
      (
        sum(n) - 2
      )
  )
  
  unname(
    (
      m[2] - m[1]
    ) /
      sp
  )
}


# ------------------------------------------------------------
# Cohen's h
# Effect size for two proportions
# ------------------------------------------------------------

cohens_h <- function(
    p1,
    p2) {
  
  2 * asin(
    sqrt(p1)
  ) -
    2 * asin(
      sqrt(p2)
    )
}


# ------------------------------------------------------------
# Set reference level only if it exists
# ------------------------------------------------------------

set_reference <- function(
    x,
    reference) {
  
  x <- factor(x)
  
  if (
    reference %in%
    levels(x)
  ) {
    
    x <- relevel(
      x,
      ref = reference
    )
  }
  
  x
}


# ============================================================
# STEP 1. DEFINE BUSINESS PROBLEM
# ============================================================

# ============================================================
# STEP 1: BUSINESS PROBLEM
# ============================================================

cat("
============================================================
STEP 1: BUSINESS PROBLEM
============================================================

INDUSTRY:
Commercial aviation / passenger airline.

PROBLEM:
The airline has post-flight passenger survey data but does not
know which service areas are associated with passenger
satisfaction.

WHY IT MATTERS:
Understanding the factors associated with satisfaction can help
management identify areas where service improvement resources
could be focused.

STAKEHOLDERS:
- Senior management
- Customer experience
- In-flight service
- Airport operations
- Digital / IT
- Marketing
- Passengers

DECISIONS:
- Which service areas require attention?
- Which passenger segments show lower satisfaction?
- Which factors are strongly associated with satisfaction?
- How can statistical evidence support management decisions?

OBJECTIVES:
1. Identify statistically significant differences between
   passenger groups.
2. Measure the strength of relationships using effect sizes.
3. Identify service areas associated with satisfaction.
4. Build a logistic regression model.
5. Compare baseline information with service information.
6. Examine alternative modelling approaches.

IMPORTANT:
This is DRIVER ANALYSIS / ASSOCIATION ANALYSIS.

The data are observational and the satisfaction and service
ratings come from the same survey. Therefore, an association
does NOT prove causation.

============================================================
")


# ============================================================
# STEP 2. IMPORT DATASET
# ============================================================


csv_file <- "airline_passenger_satisfaction.csv"

if (!file.exists(csv_file)) {
  message("CSV not found in: ", getwd(), "\nPlease select the dataset file in the window that opens.")
  csv_file <- file.choose()
}

# Save all output files (CSV results) next to the dataset
setwd(dirname(normalizePath(csv_file)))
cat("Working folder:", getwd(), "\n")

airline <- read.csv(basename(csv_file))


# Basic inspection

head(
  airline
)

tail(
  airline
)

dim(
  airline
)

nrow(
  airline
)

ncol(
  airline
)

names(
  airline
)

str(
  airline
)


# ============================================================
# STEP 3. UNDERSTAND VARIABLES
# ============================================================


summary(
  airline
)


# ------------------------------------------------------------
# Categorical variables
# ------------------------------------------------------------

table(
  airline$Gender
)

table(
  airline$Customer.Type
)

table(
  airline$Type.of.Travel
)

table(
  airline$Class
)

table(
  airline$Satisfaction
)


# ------------------------------------------------------------
# Numerical variables
# ------------------------------------------------------------

summary(
  airline$Age
)

summary(
  airline$Flight.Distance
)

summary(
  airline$Departure.Delay
)

summary(
  airline$Arrival.Delay
)


# ------------------------------------------------------------
# Set correct data types
# ------------------------------------------------------------

airline$Gender <- factor(
  airline$Gender
)

airline$Customer.Type <- factor(
  airline$Customer.Type
)

airline$Type.of.Travel <- factor(
  airline$Type.of.Travel
)

airline$Class <- factor(
  airline$Class
)


# ------------------------------------------------------------
# Standardise Satisfaction labels
#
# This makes the script robust if the CSV uses different
# capitalisation such as "satisfied".
# ------------------------------------------------------------

satisfaction_raw <- trimws(
  as.character(
    airline$Satisfaction
  )
)

airline$Satisfaction <- factor(
  
  ifelse(
    tolower(
      satisfaction_raw
    ) ==
      "satisfied",
    
    "Satisfied",
    
    "Neutral or Dissatisfied"
  ),
  
  levels = c(
    "Neutral or Dissatisfied",
    "Satisfied"
  )
)


# ------------------------------------------------------------
# Binary target
#
# 0 = Neutral or Dissatisfied
# 1 = Satisfied
# ------------------------------------------------------------

airline$y <- as.integer(
  airline$Satisfaction ==
    "Satisfied"
)


# ------------------------------------------------------------
# Set sensible reference categories when available
# ------------------------------------------------------------

airline$Gender <- set_reference(
  airline$Gender,
  "Female"
)

airline$Customer.Type <- set_reference(
  airline$Customer.Type,
  "Loyal Customer"
)

airline$Type.of.Travel <- set_reference(
  airline$Type.of.Travel,
  "Personal Travel"
)

airline$Class <- set_reference(
  airline$Class,
  "Eco"
)


# ------------------------------------------------------------
# Service variables
# ------------------------------------------------------------

service_vars <- c(
  
  "Departure.and.Arrival.Time.Convenience",
  
  "Ease.of.Online.Booking",
  
  "Check.in.Service",
  
  "Online.Boarding",
  
  "Gate.Location",
  
  "On.board.Service",
  
  "Seat.Comfort",
  
  "Leg.Room.Service",
  
  "Cleanliness",
  
  "Food.and.Drink",
  
  "In.flight.Service",
  
  "In.flight.Wifi.Service",
  
  "In.flight.Entertainment",
  
  "Baggage.Handling"
  
)


# ------------------------------------------------------------
# Data dictionary
# ------------------------------------------------------------

data_dictionary <- data.frame(
  
  Variable = c(
    
    "ID",
    
    "Gender",
    
    "Age",
    
    "Customer.Type",
    
    "Type.of.Travel",
    
    "Class",
    
    "Flight.Distance",
    
    "Departure.Delay",
    
    "Arrival.Delay",
    
    service_vars,
    
    "Satisfaction"
    
  ),
  
  Type = c(
    
    "Identifier",
    
    "Categorical",
    
    "Continuous",
    
    "Categorical",
    
    "Categorical",
    
    "Categorical / Ordinal",
    
    "Continuous",
    
    "Continuous",
    
    "Continuous",
    
    rep(
      "Ordinal 1-5 (0 = N/A)",
      length(service_vars)
    ),
    
    "Binary Target"
    
  )
  
)

print(
  data_dictionary
)


# ============================================================
# STEP 4. DATA QUALITY ASSESSMENT
# ============================================================


cat("
============================================================
STEP 4: DATA QUALITY ASSESSMENT
============================================================
")


# ------------------------------------------------------------
# Basic dimensions
# ------------------------------------------------------------

cat(
  "Rows:",
  nrow(airline),
  "| Columns:",
  ncol(airline),
  "\n"
)


# ------------------------------------------------------------
# Duplicate checks
# ------------------------------------------------------------

cat(
  "\nExact duplicate rows:",
  sum(
    duplicated(airline)
  ),
  "\n"
)

cat(
  "Duplicate IDs:",
  sum(
    duplicated(airline$ID)
  ),
  "\n"
)


# ------------------------------------------------------------
# Missing values
# ------------------------------------------------------------

missing_values <- colSums(
  is.na(airline)
)

missing_percentage <-
  100 *
  missing_values /
  nrow(airline)

missing_table <- data.frame(
  
  Variable =
    names(
      missing_values
    ),
  
  Missing =
    as.numeric(
      missing_values
    ),
  
  Percentage =
    round(
      missing_percentage,
      3
    )
  
)

missing_table <- missing_table %>%
  filter(
    Missing > 0
  )

cat(
  "\n--- Missing values ---\n"
)

print(
  missing_table
)


# ------------------------------------------------------------
# Plot missing values
# ------------------------------------------------------------

missing_df <- data.frame(
  
  Variable =
    names(
      missing_values
    ),
  
  Missing =
    as.numeric(
      missing_values
    )
  
)

missing_df <- missing_df %>%
  filter(
    Missing > 0
  )


if (
  nrow(missing_df) > 0
) {
  
  p_missing <- ggplot(
    missing_df,
    aes(
      x = Variable,
      y = Missing
    )
  ) +
    
    geom_bar(
      stat = "identity"
    ) +
    
    labs(
      
      title =
        "Missing Values by Variable",
      
      x =
        "Variable",
      
      y =
        "Number of Missing Values"
      
    ) +
    
    theme_minimal()
  
  
  print(
    p_missing
  )
}


# ------------------------------------------------------------
# Impossible / suspicious values
# ------------------------------------------------------------

cat(
  "\n--- Impossible / suspicious values ---\n"
)


cat(
  "Age < 1 or > 110:",
  sum(
    airline$Age < 1 |
      airline$Age > 110,
    na.rm = TRUE
  ),
  "\n"
)


cat(
  "Flight.Distance <= 0:",
  sum(
    airline$Flight.Distance <= 0,
    na.rm = TRUE
  ),
  "\n"
)


cat(
  "Departure.Delay < 0:",
  sum(
    airline$Departure.Delay < 0,
    na.rm = TRUE
  ),
  "\n"
)


cat(
  "Arrival.Delay < 0:",
  sum(
    airline$Arrival.Delay < 0,
    na.rm = TRUE
  ),
  "\n"
)


# ------------------------------------------------------------
# Check service rating range
# ------------------------------------------------------------

service_range_check <- sapply(
  
  airline[service_vars],
  
  function(x) {
    
    sum(
      x < 0 |
        x > 5,
      na.rm = TRUE
    )
    
  }
  
)

cat(
  "\nService ratings outside 0-5:\n"
)

print(
  service_range_check
)


# ------------------------------------------------------------
# Check zero values in service ratings
#
# IMPORTANT:
# We need to confirm from the dataset documentation that
# 0 means "Not Applicable / Not Used".
# ------------------------------------------------------------

zero_table <- data.frame(
  
  Variable =
    service_vars,
  
  Min_Value =
    sapply(
      airline[service_vars],
      min,
      na.rm = TRUE
    ),
  
  Number_of_Zeros =
    sapply(
      airline[service_vars],
      function(x)
        sum(
          x == 0,
          na.rm = TRUE
        )
    )
  
)

zero_table$Percentage_Zero <-
  round(
    100 *
      zero_table$Number_of_Zeros /
      nrow(airline),
    2
  )

cat(
  "\n--- Zero values in service ratings ---\n"
)

print(
  zero_table
)


# ------------------------------------------------------------
# Investigate missing Arrival.Delay
#
# This analysis is done BEFORE imputation.
# It checks whether missing Arrival.Delay is associated with
# observed variables.
# ------------------------------------------------------------

cat(
  "\n--- Investigation of missing Arrival.Delay ---\n"
)

tmp_missing <- data.frame(
  
  dep_delay =
    airline$Departure.Delay,
  
  arrival_missing =
    is.na(
      airline$Arrival.Delay
    ),
  
  y =
    airline$y
  
)


cat(
  "\nMean Departure.Delay by Arrival.Delay missingness:\n"
)

print(
  tapply(
    tmp_missing$dep_delay,
    tmp_missing$arrival_missing,
    mean,
    na.rm = TRUE
  )
)


cat(
  "\nWelch t-test of Departure.Delay by Arrival.Delay missingness:\n"
)

print(
  t.test(
    dep_delay ~ arrival_missing,
    data = tmp_missing
  )
)


cat(
  "\nWilcoxon test:\n"
)

print(
  suppressWarnings(
    wilcox.test(
      dep_delay ~ arrival_missing,
      data = tmp_missing
    )
  )
)


cat(
  "\nChi-square test of Arrival.Delay missingness vs Satisfaction:\n"
)

print(
  chisq.test(
    table(
      tmp_missing$arrival_missing,
      tmp_missing$y
    )
  )
)


# ------------------------------------------------------------
# Relationship between departure and arrival delay
# ------------------------------------------------------------

delay_correlation <- cor(
  
  airline$Departure.Delay,
  
  airline$Arrival.Delay,
  
  use =
    "complete.obs",
  
  method =
    "spearman"
  
)

cat(
  "\nSpearman correlation between Departure.Delay and Arrival.Delay:",
  round(
    delay_correlation,
    3
  ),
  "\n"
)


# ============================================================
# STEP 5. MISSING VALUES
#
# IMPORTANT METHODOLOGICAL CHANGE:
#
# We inspect missing values first.
#
# Then:
# 1. Remove exact duplicates BEFORE split
# 2. Split 80/20
# 3. Learn imputation rules from TRAIN only
# 4. Apply those rules to TRAIN and TEST
#
# This prevents data leakage.
# ============================================================


cat("
============================================================
STEP 5: MISSING VALUES + TRAIN/TEST SPLIT + PREPROCESSING
============================================================
")


# ------------------------------------------------------------
# Remove exact duplicate rows BEFORE train/test split
#
# This prevents identical observations from appearing in both
# training and test sets.
#
# The original Step 6 duplicate section is retained later as
# a verification step.
# ------------------------------------------------------------

airline_nodup <- airline %>%
  
  distinct()


cat(
  "Rows before duplicate removal:",
  nrow(airline),
  "\n"
)

cat(
  "Rows after duplicate removal:",
  nrow(airline_nodup),
  "\n"
)


# ------------------------------------------------------------
# 5.1 Stratified train/test split
# ------------------------------------------------------------

set.seed(
  SEED
)

train_index <- createDataPartition(
  
  airline_nodup$Satisfaction,
  
  p = 0.80,
  
  list = FALSE
  
)


train_raw <- airline_nodup[
  train_index,
]

test_raw <- airline_nodup[
  -train_index,
]


cat(
  "\nTraining rows:",
  nrow(train_raw),
  "\n"
)

cat(
  "Testing rows:",
  nrow(test_raw),
  "\n"
)


# ------------------------------------------------------------
# Check satisfaction proportions
# ------------------------------------------------------------

cat(
  "\nTraining satisfaction proportions:\n"
)

print(
  round(
    prop.table(
      table(
        train_raw$Satisfaction
      )
    ),
    4
  )
)


cat(
  "\nTesting satisfaction proportions:\n"
)

print(
  round(
    prop.table(
      table(
        test_raw$Satisfaction
      )
    ),
    4
  )
)


# ------------------------------------------------------------
# 5.2 Learn preprocessing rules from TRAIN ONLY
# ------------------------------------------------------------

learn_preprocessing <- function(
    train_data) {
  
  
  # Count zero values
  zero_counts <- sapply(
    
    train_data[service_vars],
    
    function(x)
      sum(
        x == 0,
        na.rm = TRUE
      )
    
  )
  
  
  # Create N/A flags for variables with enough zeros
  flag_columns <- if (
    ZERO_MEANS_NA
  ) {
    
    names(zero_counts)[
      zero_counts >=
        ZERO_FLAG_MIN
    ]
    
  } else {
    
    character(0)
    
  }
  
  
  # Copy training data
  temp <- train_data
  
  
  # ----------------------------------------------------------
  # Convert 0 to NA
  # ----------------------------------------------------------
  
  if (
    ZERO_MEANS_NA
  ) {
    
    for (
      v in service_vars
    ) {
      
      temp[[v]][
        temp[[v]] == 0
      ] <- NA
      
    }
    
  }
  
  
  # ----------------------------------------------------------
  # Calculate service-rating medians from TRAIN ONLY
  # ----------------------------------------------------------
  
  service_medians <- sapply(
    
    temp[service_vars],
    
    function(x)
      round(
        median(
          x,
          na.rm = TRUE
        )
      )
    
  )
  
  
  # ----------------------------------------------------------
  # Regression model for missing Arrival.Delay
  #
  # IMPORTANT:
  # Model is fitted using TRAINING rows only.
  # ----------------------------------------------------------
  
  arrival_model <- lm(
    
    Arrival.Delay ~
      Departure.Delay,
    
    data =
      temp[
        !is.na(
          temp$Arrival.Delay
        ),
      ]
    
  )
  
  
  list(
    
    flag_columns =
      flag_columns,
    
    service_medians =
      service_medians,
    
    arrival_model =
      arrival_model
    
  )
  
}


# ------------------------------------------------------------
# 5.3 Apply preprocessing to data
# ------------------------------------------------------------

apply_preprocessing <- function(
    data,
    prep) {
  
  
  d <- data
  
  
  # ----------------------------------------------------------
  # A. Create N/A flags
  # ----------------------------------------------------------
  
  for (
    v in prep$flag_columns
  ) {
    
    d[[paste0(v, "_NA")]] <-
      as.integer(
        d[[v]] == 0
      )
    
  }
  
  
  # ----------------------------------------------------------
  # B. Convert 0 to NA
  # ----------------------------------------------------------
  
  if (
    ZERO_MEANS_NA
  ) {
    
    for (
      v in service_vars
    ) {
      
      d[[v]][
        d[[v]] == 0
      ] <- NA
      
    }
    
  }
  
  
  # ----------------------------------------------------------
  # C. Median imputation for service ratings
  #
  # Medians come from TRAINING data only.
  # ----------------------------------------------------------
  
  for (
    v in service_vars
  ) {
    
    d[[v]][
      is.na(
        d[[v]]
      )
    ] <-
      prep$service_medians[[v]]
    
  }
  
  
  # ----------------------------------------------------------
  # D. Regression imputation for Arrival.Delay
  #
  # Model was learned from TRAIN only.
  # ----------------------------------------------------------
  
  missing_arrival <- is.na(
    d$Arrival.Delay
  )
  
  
  if (
    any(
      missing_arrival
    )
  ) {
    
    predicted_arrival <-
      predict(
        
        prep$arrival_model,
        
        newdata =
          d[
            missing_arrival,
            ,
            drop = FALSE
          ]
        
      )
    
    
    # Arrival delay cannot be negative
    d$Arrival.Delay[
      missing_arrival
    ] <-
      pmax(
        0,
        predicted_arrival
      )
    
  }
  
  
  # ----------------------------------------------------------
  # E. Log transformations
  #
  # log1p(x) handles zero values safely.
  # ----------------------------------------------------------
  
  d$log_Departure.Delay <-
    log1p(
      d$Departure.Delay
    )
  
  
  d$log_Arrival.Delay <-
    log1p(
      d$Arrival.Delay
    )
  
  
  d$log_Flight.Distance <-
    log(
      d$Flight.Distance
    )
  
  
  # ----------------------------------------------------------
  # F. Overall service score
  # ----------------------------------------------------------
  
  d$Service.Score <-
    
    rowMeans(
      d[
        service_vars
      ]
    )
  
  
  d
  
}


# ------------------------------------------------------------
# Learn preprocessing from TRAIN only
# ------------------------------------------------------------

prep <- learn_preprocessing(
  train_raw
)


# ------------------------------------------------------------
# Apply identical preprocessing rules to TRAIN and TEST
# ------------------------------------------------------------

train <- apply_preprocessing(
  train_raw,
  prep
)

test <- apply_preprocessing(
  test_raw,
  prep
)


# ------------------------------------------------------------
# Save N/A flag variable names
# ------------------------------------------------------------

flag_vars <- paste0(
  prep$flag_columns,
  "_NA"
)


# ------------------------------------------------------------
# Missing-value checks after preprocessing
# ------------------------------------------------------------

cat(
  "\nMissing Arrival.Delay in TRAIN:",
  sum(
    is.na(
      train$Arrival.Delay
    )
  ),
  "\n"
)

cat(
  "Missing Arrival.Delay in TEST:",
  sum(
    is.na(
      test$Arrival.Delay
    )
  ),
  "\n"
)


cat(
  "Missing service ratings in TRAIN:",
  sum(
    is.na(
      train[
        service_vars
      ]
    )
  ),
  "\n"
)


cat(
  "Missing service ratings in TEST:",
  sum(
    is.na(
      test[
        service_vars
      ]
    )
  ),
  "\n"
)


cat(
  "\nTraining medians used for service-rating imputation:\n"
)

print(
  prep$service_medians
)


cat(
  "\nN/A flag variables created:\n"
)

print(
  flag_vars
)


# ------------------------------------------------------------
# IMPORTANT:
# Keep the original object name "airline_clean" so Pulindu's
# later code structure remains familiar.
#
# All EDA/inference below uses TRAINING data only.
# TEST remains untouched for Vidu's later evaluation.
# ------------------------------------------------------------

airline_clean <- train


# ============================================================
# STEP 6. DUPLICATES
# ============================================================


cat("
============================================================
STEP 6: DUPLICATES
============================================================
")


# Original duplicate checks retained

cat(
  "Exact duplicate rows in original dataset:",
  sum(
    duplicated(airline)
  ),
  "\n"
)


cat(
  "Duplicate IDs:",
  sum(
    duplicated(airline$ID)
  ),
  "\n"
)


# Show duplicate rows if any

duplicates <- airline[
  duplicated(
    airline
  ),
]

if (
  nrow(duplicates) > 0
) {
  
  print(
    duplicates
  )
  
}


# Confirm no exact duplicates remain in the modelling data

cat(
  "Duplicates remaining in cleaned TRAIN data:",
  sum(
    duplicated(
      airline_clean
    )
  ),
  "\n"
)


# Safety check

airline_clean <- airline_clean %>%
  distinct()


cat(
  "Duplicates after final check:",
  sum(
    duplicated(
      airline_clean
    )
  ),
  "\n"
)


# ============================================================
# STEP 7. OUTLIER ANALYSIS
# ============================================================


cat("
============================================================
STEP 7: OUTLIER ANALYSIS
============================================================
")


# ------------------------------------------------------------
# IQR function
# ------------------------------------------------------------

find_outliers <- function(
    x) {
  
  Q1 <- quantile(
    x,
    0.25,
    na.rm = TRUE
  )
  
  Q3 <- quantile(
    x,
    0.75,
    na.rm = TRUE
  )
  
  IQR_value <-
    Q3 - Q1
  
  lower <-
    Q1 -
    1.5 *
    IQR_value
  
  upper <-
    Q3 +
    1.5 *
    IQR_value
  
  outliers <- x[
    x < lower |
      x > upper
  ]
  
  return(
    list(
      
      Q1 = Q1,
      
      Q3 = Q3,
      
      IQR = IQR_value,
      
      Lower_Bound =
        lower,
      
      Upper_Bound =
        upper,
      
      Number_of_Outliers =
        length(
          outliers
        )
      
    )
  )
  
}


# ------------------------------------------------------------
# Age
# ------------------------------------------------------------

p_age_box <- ggplot(
  airline_clean,
  aes(
    y = Age
  )
) +
  
  geom_boxplot() +
  
  labs(
    
    title =
      "Boxplot of Passenger Age",
    
    y =
      "Age"
    
  ) +
  
  theme_minimal()


print(
  p_age_box
)


# ------------------------------------------------------------
# Flight Distance
# ------------------------------------------------------------

p_distance_box <- ggplot(
  airline_clean,
  aes(
    y = Flight.Distance
  )
) +
  
  geom_boxplot() +
  
  labs(
    
    title =
      "Boxplot of Flight Distance",
    
    y =
      "Flight Distance"
    
  ) +
  
  theme_minimal()


print(
  p_distance_box
)


# ------------------------------------------------------------
# Departure Delay
# ------------------------------------------------------------

p_departure_box <- ggplot(
  airline_clean,
  aes(
    y = Departure.Delay
  )
) +
  
  geom_boxplot() +
  
  labs(
    
    title =
      "Boxplot of Departure Delay",
    
    y =
      "Departure Delay"
    
  ) +
  
  theme_minimal()


print(
  p_departure_box
)


# ------------------------------------------------------------
# Arrival Delay
# ------------------------------------------------------------

p_arrival_box <- ggplot(
  airline_clean,
  aes(
    y = Arrival.Delay
  )
) +
  
  geom_boxplot() +
  
  labs(
    
    title =
      "Boxplot of Arrival Delay",
    
    y =
      "Arrival Delay"
    
  ) +
  
  theme_minimal()


print(
  p_arrival_box
)


# ------------------------------------------------------------
# IQR results
# ------------------------------------------------------------

find_outliers(
  airline_clean$Age
)

find_outliers(
  airline_clean$Flight.Distance
)

find_outliers(
  airline_clean$Departure.Delay
)

find_outliers(
  airline_clean$Arrival.Delay
)


# ------------------------------------------------------------
# Outlier summary table
# ------------------------------------------------------------

numeric_variables <- c(
  
  "Age",
  
  "Flight.Distance",
  
  "Departure.Delay",
  
  "Arrival.Delay"
  
)


outlier_table <- data.frame(
  
  Variable =
    numeric_variables,
  
  IQR_Outliers =
    sapply(
      
      airline_clean[
        numeric_variables
      ],
      
      function(x) {
        
        q <- quantile(
          x,
          c(
            0.25,
            0.75
          ),
          na.rm = TRUE
        )
        
        i <- IQR(
          x,
          na.rm = TRUE
        )
        
        sum(
          x <
            q[1] -
            1.5 *
            i |
            
            x >
            q[2] +
            1.5 *
            i,
          
          na.rm = TRUE
        )
        
      }
      
    ),
  
  Zscore_Outliers =
    sapply(
      
      airline_clean[
        numeric_variables
      ],
      
      function(x) {
        
        z <- as.numeric(
          scale(x)
        )
        
        sum(
          abs(z) > 3,
          na.rm = TRUE
        )
        
      }
      
    ),
  
  Maximum =
    sapply(
      
      airline_clean[
        numeric_variables
      ],
      
      max,
      na.rm = TRUE
      
    )
  
)


print(
  outlier_table
)


cat(
  "\nDeparture delays over 3 hours:",
  sum(
    airline_clean$Departure.Delay >
      180
  ),
  "\n"
)


cat(
  "Departure delays over 8 hours:",
  sum(
    airline_clean$Departure.Delay >
      480
  ),
  "\n"
)


# IMPORTANT INTERPRETATION:
#
# Extreme delays are not automatically treated as data-entry
# errors. They can represent real operational events.
#
# Therefore, we keep the observations and use log
# transformations in modelling to reduce the influence of
# extreme right-skewed values.


# ============================================================
# STEP 8. DESCRIPTIVE STATISTICS
# ============================================================


cat("
============================================================
STEP 8: DESCRIPTIVE STATISTICS
============================================================
")


# ------------------------------------------------------------
# Original summary
# ------------------------------------------------------------

summary(
  airline_clean
)


# ------------------------------------------------------------
# Numerical variables
# ------------------------------------------------------------

numeric_data <- airline_clean %>%
  
  select(
    
    Age,
    
    Flight.Distance,
    
    Departure.Delay,
    
    Arrival.Delay
    
  )


summary(
  numeric_data
)


# ------------------------------------------------------------
# Mean
# ------------------------------------------------------------

sapply(
  
  numeric_data,
  
  mean,
  
  na.rm = TRUE
  
)


# ------------------------------------------------------------
# Median
# ------------------------------------------------------------

sapply(
  
  numeric_data,
  
  median,
  
  na.rm = TRUE
  
)


# ------------------------------------------------------------
# Standard deviation
# ------------------------------------------------------------

sapply(
  
  numeric_data,
  
  sd,
  
  na.rm = TRUE
  
)


# ------------------------------------------------------------
# Minimum
# ------------------------------------------------------------

sapply(
  
  numeric_data,
  
  min,
  
  na.rm = TRUE
  
)


# ------------------------------------------------------------
# Maximum
# ------------------------------------------------------------

sapply(
  
  numeric_data,
  
  max,
  
  na.rm = TRUE
  
)


# ------------------------------------------------------------
# psych::describe
# ------------------------------------------------------------

describe(
  numeric_data
)


# ------------------------------------------------------------
# More detailed descriptive statistics
# Added from second method
# ------------------------------------------------------------

desc_table <- numeric_data %>%
  
  pivot_longer(
    
    everything(),
    
    names_to =
      "Variable",
    
    values_to =
      "Value"
    
  ) %>%
  
  group_by(
    Variable
  ) %>%
  
  summarise(
    
    N =
      n(),
    
    Mean =
      mean(Value),
    
    SD =
      sd(Value),
    
    Median =
      median(Value),
    
    IQR =
      IQR(Value),
    
    Min =
      min(Value),
    
    Max =
      max(Value),
    
    Skewness =
      e1071::skewness(Value),
    
    Kurtosis =
      e1071::kurtosis(Value),
    
    .groups =
      "drop"
    
  )


print(
  desc_table
)


# ------------------------------------------------------------
# Service-rating descriptive statistics
# ------------------------------------------------------------

service_desc <- airline_clean %>%
  
  select(
    all_of(
      service_vars
    )
  ) %>%
  
  pivot_longer(
    
    everything(),
    
    names_to =
      "Service",
    
    values_to =
      "Rating"
    
  ) %>%
  
  group_by(
    Service
  ) %>%
  
  summarise(
    
    Mean =
      mean(Rating),
    
    SD =
      sd(Rating),
    
    Median =
      median(Rating),
    
    Percentage_4_or_5 =
      100 *
      mean(
        Rating >= 4
      ),
    
    .groups =
      "drop"
    
  ) %>%
  
  arrange(
    Mean
  )


print(
  service_desc
)


# ------------------------------------------------------------
# Satisfaction statistics
# ------------------------------------------------------------

satisfaction_table <-
  table(
    airline_clean$Satisfaction
  )

print(
  satisfaction_table
)


satisfaction_percentage <-
  prop.table(
    satisfaction_table
  ) *
  100

print(
  satisfaction_percentage
)


# ------------------------------------------------------------
# Satisfaction prevalence
# ------------------------------------------------------------

prev <- mean(
  airline_clean$y
)


cat(
  "\nSatisfied share:",
  round(
    100 *
      prev,
    2
  ),
  "%\n"
)


# ------------------------------------------------------------
# Imbalance ratio
# ------------------------------------------------------------

imbalance_ratio <-
  
  max(
    prev,
    1 - prev
  ) /
  
  min(
    prev,
    1 - prev
  )


cat(
  "Majority : Minority ratio:",
  round(
    imbalance_ratio,
    2
  ),
  ": 1\n"
)


cat(
  "Majority-class baseline accuracy:",
  round(
    100 *
      max(
        prev,
        1 - prev
      ),
    2
  ),
  "%\n"
)


# ============================================================
# STEP 9. EDA & VISUALIZATIONS
# ============================================================


cat("
============================================================
STEP 9: EDA & VISUALIZATIONS
============================================================
")


# ------------------------------------------------------------
# Satisfaction
# ------------------------------------------------------------

ggplot(
  airline_clean,
  aes(
    x = Satisfaction
  )
) +
  
  geom_bar() +
  
  labs(
    
    title =
      "Passenger Satisfaction Distribution",
    
    x =
      "Satisfaction",
    
    y =
      "Number of Passengers"
    
  ) +
  
  theme_minimal()


# ------------------------------------------------------------
# Gender
# ------------------------------------------------------------

ggplot(
  airline_clean,
  aes(
    
    x =
      Gender,
    
    fill =
      Satisfaction
    
  )
) +
  
  geom_bar(
    position =
      "dodge"
  ) +
  
  labs(
    
    title =
      "Passenger Satisfaction by Gender",
    
    x =
      "Gender",
    
    y =
      "Number of Passengers"
    
  ) +
  
  theme_minimal()


# ------------------------------------------------------------
# Customer Type
# ------------------------------------------------------------

ggplot(
  airline_clean,
  aes(
    
    x =
      Customer.Type,
    
    fill =
      Satisfaction
    
  )
) +
  
  geom_bar(
    position =
      "dodge"
  ) +
  
  labs(
    
    title =
      "Passenger Satisfaction by Customer Type",
    
    x =
      "Customer Type",
    
    y =
      "Number of Passengers"
    
  ) +
  
  theme_minimal()


# ------------------------------------------------------------
# Type of Travel
# ------------------------------------------------------------

ggplot(
  airline_clean,
  aes(
    
    x =
      Type.of.Travel,
    
    fill =
      Satisfaction
    
  )
) +
  
  geom_bar(
    position =
      "dodge"
  ) +
  
  labs(
    
    title =
      "Passenger Satisfaction by Type of Travel",
    
    x =
      "Type of Travel",
    
    y =
      "Number of Passengers"
    
  ) +
  
  theme_minimal()


# ------------------------------------------------------------
# Class
# ------------------------------------------------------------

ggplot(
  airline_clean,
  aes(
    
    x =
      Class,
    
    fill =
      Satisfaction
    
  )
) +
  
  geom_bar(
    position =
      "dodge"
  ) +
  
  labs(
    
    title =
      "Passenger Satisfaction by Class",
    
    x =
      "Class",
    
    y =
      "Number of Passengers"
    
  ) +
  
  theme_minimal()


# ------------------------------------------------------------
# Age distribution
# ------------------------------------------------------------

ggplot(
  airline_clean,
  aes(
    x =
      Age
  )
) +
  
  geom_histogram(
    bins =
      30
  ) +
  
  labs(
    
    title =
      "Distribution of Passenger Age",
    
    x =
      "Age",
    
    y =
      "Number of Passengers"
    
  ) +
  
  theme_minimal()


# ------------------------------------------------------------
# Flight distance
# ------------------------------------------------------------

ggplot(
  airline_clean,
  aes(
    x =
      Flight.Distance
  )
) +
  
  geom_histogram(
    bins =
      30
  ) +
  
  labs(
    
    title =
      "Distribution of Flight Distance",
    
    x =
      "Flight Distance",
    
    y =
      "Number of Passengers"
    
  ) +
  
  theme_minimal()


# ------------------------------------------------------------
# Departure delay
# ------------------------------------------------------------

ggplot(
  airline_clean,
  aes(
    x =
      Departure.Delay
  )
) +
  
  geom_histogram(
    bins =
      30
  ) +
  
  labs(
    
    title =
      "Distribution of Departure Delay",
    
    x =
      "Departure Delay",
    
    y =
      "Number of Passengers"
    
  ) +
  
  theme_minimal()


# ------------------------------------------------------------
# Arrival delay
# ------------------------------------------------------------

ggplot(
  airline_clean,
  aes(
    x =
      Arrival.Delay
  )
) +
  
  geom_histogram(
    bins =
      30
  ) +
  
  labs(
    
    title =
      "Distribution of Arrival Delay",
    
    x =
      "Arrival Delay",
    
    y =
      "Number of Passengers"
    
  ) +
  
  theme_minimal()


# ------------------------------------------------------------
# Age vs Satisfaction
# ------------------------------------------------------------

ggplot(
  airline_clean,
  aes(
    
    x =
      Satisfaction,
    
    y =
      Age
    
  )
) +
  
  geom_boxplot() +
  
  labs(
    
    title =
      "Age Distribution by Passenger Satisfaction",
    
    x =
      "Satisfaction",
    
    y =
      "Age"
    
  ) +
  
  theme_minimal()


# ------------------------------------------------------------
# Flight Distance vs Satisfaction
# ------------------------------------------------------------

ggplot(
  airline_clean,
  aes(
    
    x =
      Satisfaction,
    
    y =
      Flight.Distance
    
  )
) +
  
  geom_boxplot() +
  
  labs(
    
    title =
      "Flight Distance by Passenger Satisfaction",
    
    x =
      "Satisfaction",
    
    y =
      "Flight Distance"
    
  ) +
  
  theme_minimal()


# ------------------------------------------------------------
# Departure Delay vs Satisfaction
# ------------------------------------------------------------

ggplot(
  airline_clean,
  aes(
    
    x =
      Satisfaction,
    
    y =
      Departure.Delay
    
  )
) +
  
  geom_boxplot() +
  
  labs(
    
    title =
      "Departure Delay by Passenger Satisfaction",
    
    x =
      "Satisfaction",
    
    y =
      "Departure Delay"
    
  ) +
  
  theme_minimal()


# ------------------------------------------------------------
# Arrival Delay vs Satisfaction
# ------------------------------------------------------------

ggplot(
  airline_clean,
  aes(
    
    x =
      Satisfaction,
    
    y =
      Arrival.Delay
    
  )
) +
  
  geom_boxplot() +
  
  labs(
    
    title =
      "Arrival Delay by Passenger Satisfaction",
    
    x =
      "Satisfaction",
    
    y =
      "Arrival Delay"
    
  ) +
  
  theme_minimal()


# ------------------------------------------------------------
# Satisfaction RATE by segment
# Added from second method
# ------------------------------------------------------------

segment_rate <- airline_clean %>%
  
  select(
    
    y,
    
    Gender,
    
    Customer.Type,
    
    Type.of.Travel,
    
    Class
    
  ) %>%
  
  mutate(
    
    across(
      -y,
      as.character
    )
    
  ) %>%
  
  pivot_longer(
    
    -y,
    
    names_to =
      "Variable",
    
    values_to =
      "Level"
    
  ) %>%
  
  group_by(
    
    Variable,
    
    Level
    
  ) %>%
  
  summarise(
    
    Satisfaction_Rate =
      mean(y),
    
    N =
      n(),
    
    .groups =
      "drop"
    
  )


print(
  segment_rate
)


ggplot(
  
  segment_rate,
  
  aes(
    
    x =
      Level,
    
    y =
      Satisfaction_Rate
    
  )
  
) +
  
  geom_col() +
  
  geom_hline(
    
    yintercept =
      prev,
    
    linetype =
      2
    
  ) +
  
  facet_wrap(
    ~Variable,
    scales =
      "free_x"
  ) +
  
  scale_y_continuous(
    
    labels =
      scales::percent
    
  ) +
  
  labs(
    
    title =
      "Satisfaction Rate by Passenger Segment",
    
    x =
      NULL,
    
    y =
      "% Satisfied"
    
  ) +
  
  theme_minimal()


# ------------------------------------------------------------
# Mean service ratings by satisfaction group
# Added from second method
# ------------------------------------------------------------

rating_group <- airline_clean %>%
  
  select(
    
    Satisfaction,
    
    all_of(
      service_vars
    )
    
  ) %>%
  
  pivot_longer(
    
    -Satisfaction,
    
    names_to =
      "Service",
    
    values_to =
      "Rating"
    
  ) %>%
  
  group_by(
    
    Service,
    
    Satisfaction
    
  ) %>%
  
  summarise(
    
    Mean_Rating =
      mean(Rating),
    
    .groups =
      "drop"
    
  )


print(
  rating_group
)


ggplot(
  
  rating_group,
  
  aes(
    
    x =
      Mean_Rating,
    
    y =
      reorder(
        Service,
        Mean_Rating
      ),
    
    colour =
      Satisfaction
    
  )
  
) +
  
  geom_point(
    size =
      3
  ) +
  
  labs(
    
    title =
      "Mean Service Rating by Satisfaction Group",
    
    x =
      "Mean Rating",
    
    y =
      NULL
    
  ) +
  
  theme_minimal()


# ============================================================
# STEP 10. CORRELATION ANALYSIS
# ============================================================


cat("
============================================================
STEP 10: CORRELATION ANALYSIS
============================================================
")


# ------------------------------------------------------------
# ORIGINAL STRUCTURE RETAINED
#
# IMPORTANT CHANGE:
# Pearson -> Spearman
#
# Why?
# Service ratings are ordinal (1-5), and delay variables are
# highly skewed. Spearman is based on ranks and measures
# monotonic association.
# ------------------------------------------------------------


correlation_data <- airline_clean %>%
  
  select(
    
    Age,
    
    Flight.Distance,
    
    Departure.Delay,
    
    Arrival.Delay,
    
    all_of(
      service_vars
    )
    
  )


correlation_matrix <- cor(
  
  correlation_data,
  
  use =
    "complete.obs",
  
  method =
    "spearman"
  
)


cat(
  "\nSpearman correlation matrix:\n"
)

print(
  round(
    correlation_matrix,
    2
  )
)


# ------------------------------------------------------------
# Correlation heatmap
# ------------------------------------------------------------

corrplot(
  
  correlation_matrix,
  
  method =
    "color",
  
  type =
    "full",
  
  tl.col =
    "black",
  
  tl.srt =
    45,
  
  addCoef.col =
    "black",
  
  number.cex =
    0.5
  
)


# ------------------------------------------------------------
# Service-rating correlation specifically
# ------------------------------------------------------------

service_correlation <- cor(
  
  airline_clean[
    service_vars
  ],
  
  method =
    "spearman",
  
  use =
    "complete.obs"
  
)


cat(
  "\nSpearman correlation among service ratings:\n"
)

print(
  round(
    service_correlation,
    2
  )
)


corrplot(
  
  service_correlation,
  
  method =
    "color",
  
  type =
    "full",
  
  tl.col =
    "black",
  
  tl.srt =
    45,
  
  addCoef.col =
    "black",
  
  number.cex =
    0.5
  
)


# ------------------------------------------------------------
# Strongest service-rating pairs
# ------------------------------------------------------------

upper_indices <- which(
  
  upper.tri(
    service_correlation
  ),
  
  arr.ind =
    TRUE
  
)


top_pairs <- data.frame(
  
  Variable1 =
    rownames(
      service_correlation
    )[
      upper_indices[, 1]
    ],
  
  Variable2 =
    colnames(
      service_correlation
    )[
      upper_indices[, 2]
    ],
  
  Spearman_Rho =
    service_correlation[
      upper_indices
    ]
  
)


top_pairs <- top_pairs %>%
  
  arrange(
    
    desc(
      abs(
        Spearman_Rho
      )
    )
    
  )


cat(
  "\nTop correlated service-rating pairs:\n"
)

print(
  head(
    top_pairs,
    10
  )
)


# ------------------------------------------------------------
# Correlation of numerical variables with Satisfaction
# ------------------------------------------------------------

target_correlation <- data.frame(
  
  Variable =
    c(
      numeric_variables,
      service_vars
    ),
  
  Spearman_Correlation =
    
    sapply(
      
      airline_clean[
        c(
          numeric_variables,
          service_vars
        )
      ],
      
      function(x)
        
        cor(
          
          x,
          
          airline_clean$y,
          
          method =
            "spearman",
          
          use =
            "complete.obs"
          
        )
      
    )
  
)


target_correlation <- target_correlation %>%
  
  arrange(
    
    desc(
      abs(
        Spearman_Correlation
      )
    )
    
  )


cat(
  "\nSpearman correlation with Satisfaction:\n"
)

print(
  target_correlation
)


# ------------------------------------------------------------
# Cramer's V
#
# Used for categorical variables because Pearson/Spearman are
# not the appropriate measure for two categorical variables.
# ------------------------------------------------------------

categorical_variables <- c(
  
  "Gender",
  
  "Customer.Type",
  
  "Type.of.Travel",
  
  "Class"
  
)


cramers_results <- data.frame(
  
  Variable =
    categorical_variables,
  
  Cramers_V =
    sapply(
      
      categorical_variables,
      
      function(v)
        
        cramers_v(
          
          airline_clean[[v]],
          
          airline_clean$Satisfaction
          
        )
      
    )
  
)


cat(
  "\nCramer's V:\n"
)

print(
  cramers_results
)


# ============================================================
# STEP 11. STATISTICAL INFERENCE
# ============================================================


cat("
============================================================
STEP 11: STATISTICAL INFERENCE
============================================================
")


# ============================================================
# 11.1 CHI-SQUARE TESTS
# ============================================================


cat("
------------------------------------------------------------
11.1 CHI-SQUARE TESTS
------------------------------------------------------------
")


# ------------------------------------------------------------
# Interpretation function
# ------------------------------------------------------------

interpret_chisq <- function(
    
  test,
  
  variable_name,
  
  effect_size
  
) {
  
  cat(
    "\nChi-square Test:",
    variable_name,
    "vs Satisfaction\n"
  )
  
  
  cat(
    
    "Chi-square statistic =",
    
    round(
      as.numeric(
        test$statistic
      ),
      4
    ),
    
    "\n"
    
  )
  
  
  cat(
    
    "df =",
    
    as.numeric(
      test$parameter
    ),
    
    "\n"
    
  )
  
  
  cat(
    
    "p-value =",
    
    format.pval(
      test$p.value,
      digits =
        4
    ),
    
    "\n"
    
  )
  
  
  cat(
    
    "Cramer's V =",
    
    round(
      effect_size,
      4
    ),
    
    "\n"
    
  )
  
  
  if (
    test$p.value < 0.05
  ) {
    
    cat(
      "Decision: Reject H0.\n"
    )
    
    cat(
      "Conclusion: There is a statistically significant association.\n"
    )
    
  } else {
    
    cat(
      "Decision: Fail to reject H0.\n"
    )
    
    cat(
      "Conclusion: No statistically significant association.\n"
    )
    
  }
  
}


# ------------------------------------------------------------
# Gender vs Satisfaction
# ------------------------------------------------------------

gender_table <- table(
  
  airline_clean$Gender,
  
  airline_clean$Satisfaction
  
)

chisq_gender <- chisq.test(
  gender_table
)

interpret_chisq(
  
  chisq_gender,
  
  "Gender",
  
  cramers_v(
    airline_clean$Gender,
    airline_clean$Satisfaction
  )
  
)


# ------------------------------------------------------------
# Customer Type
# ------------------------------------------------------------

customer_type_table <- table(
  
  airline_clean$Customer.Type,
  
  airline_clean$Satisfaction
  
)

chisq_customer_type <-
  chisq.test(
    customer_type_table
  )

interpret_chisq(
  
  chisq_customer_type,
  
  "Customer Type",
  
  cramers_v(
    airline_clean$Customer.Type,
    airline_clean$Satisfaction
  )
  
)


# ------------------------------------------------------------
# Type of Travel
# ------------------------------------------------------------

travel_type_table <- table(
  
  airline_clean$Type.of.Travel,
  
  airline_clean$Satisfaction
  
)

chisq_travel_type <-
  chisq.test(
    travel_type_table
  )

interpret_chisq(
  
  chisq_travel_type,
  
  "Type of Travel",
  
  cramers_v(
    airline_clean$Type.of.Travel,
    airline_clean$Satisfaction
  )
  
)


# ------------------------------------------------------------
# Class
# ------------------------------------------------------------

class_table <- table(
  
  airline_clean$Class,
  
  airline_clean$Satisfaction
  
)

chisq_class <-
  chisq.test(
    class_table
  )

interpret_chisq(
  
  chisq_class,
  
  "Class",
  
  cramers_v(
    airline_clean$Class,
    airline_clean$Satisfaction
  )
  
)


# ============================================================
# 11.2 TWO-PROPORTION TESTS
# Added from second method
# ============================================================


cat("
------------------------------------------------------------
11.2 TWO-PROPORTION TESTS
------------------------------------------------------------
")


run_two_prop <- function(
    
  variable,
  
  label
  
) {
  
  tb <- table(
    
    airline_clean[[variable]],
    
    airline_clean$y
    
  )
  
  
  test <- prop.test(
    
    x =
      tb[, "1"],
    
    n =
      rowSums(tb),
    
    correct =
      FALSE
    
  )
  
  
  estimated <-
    unname(
      test$estimate
    )
  
  
  effect_h <-
    cohens_h(
      
      estimated[1],
      
      estimated[2]
      
    )
  
  
  cat(
    "\n",
    label,
    "\n"
  )
  
  
  cat(
    
    rownames(tb)[1],
    
    "satisfaction rate =",
    
    round(
      100 *
        estimated[1],
      2
    ),
    
    "%\n"
    
  )
  
  
  cat(
    
    rownames(tb)[2],
    
    "satisfaction rate =",
    
    round(
      100 *
        estimated[2],
      2
    ),
    
    "%\n"
    
  )
  
  
  cat(
    
    "Difference =",
    
    round(
      
      100 *
        (
          estimated[1] -
            estimated[2]
        ),
      
      2
      
    ),
    
    "percentage points\n"
    
  )
  
  
  cat(
    
    "p-value =",
    
    fmt_p(
      test$p.value
    ),
    
    "\n"
    
  )
  
  
  cat(
    
    "Cohen's h =",
    
    round(
      effect_h,
      3
    ),
    
    "\n"
    
  )
  
}


run_two_prop(
  
  "Gender",
  
  "Female vs Male"
  
)


run_two_prop(
  
  "Type.of.Travel",
  
  "Personal vs Business Travel"
  
)


run_two_prop(
  
  "Customer.Type",
  
  "Customer Type"
  
)


# ============================================================
# 11.3 INDEPENDENT SAMPLES T-TESTS
# ============================================================


cat("
------------------------------------------------------------
11.3 INDEPENDENT SAMPLES T-TESTS
------------------------------------------------------------
")


# ------------------------------------------------------------
# Interpretation function
#
# t.test() defaults to Welch's t-test.
# It does not assume equal variances.
# ------------------------------------------------------------

interpret_ttest <- function(
    
  variable,
  
  label
  
) {
  
  formula <- as.formula(
    
    paste(
      variable,
      "~ Satisfaction"
    )
    
  )
  
  
  x <- airline_clean[[variable]]
  
  
  test <- t.test(
    
    formula,
    
    data =
      airline_clean
    
  )
  
  
  wilcox <- wilcox.test(
    
    formula,
    
    data =
      airline_clean
    
  )
  
  
  d <- cohens_d(
    
    x,
    
    airline_clean$Satisfaction
    
  )
  
  
  cat(
    
    "\n",
    label,
    "\n"
    
  )
  
  
  cat(
    
    "Mean Not_Satisfied =",
    
    round(
      test$estimate[1],
      3
    ),
    
    "\n"
    
  )
  
  
  cat(
    
    "Mean Satisfied =",
    
    round(
      test$estimate[2],
      3
    ),
    
    "\n"
    
  )
  
  
  cat(
    
    "Welch t-statistic =",
    
    round(
      as.numeric(
        test$statistic
      ),
      3
    ),
    
    "\n"
    
  )
  
  
  cat(
    
    "p-value =",
    
    fmt_p(
      test$p.value
    ),
    
    "\n"
    
  )
  
  
  cat(
    
    "95% CI = [",
    
    round(
      test$conf.int[1],
      3
    ),
    
    ", ",
    
    round(
      test$conf.int[2],
      3
    ),
    
    "]\n"
    
  )
  
  
  cat(
    
    "Cohen's d =",
    
    round(
      d,
      3
    ),
    
    "\n"
    
  )
  
  
  cat(
    
    "Wilcoxon p-value =",
    
    fmt_p(
      wilcox$p.value
    ),
    
    "\n"
    
  )
  
}


interpret_ttest(
  
  "Age",
  
  "Age"
  
)


interpret_ttest(
  
  "Flight.Distance",
  
  "Flight Distance"
  
)


interpret_ttest(
  
  "Departure.Delay",
  
  "Departure Delay"
  
)


interpret_ttest(
  
  "Arrival.Delay",
  
  "Arrival Delay"
  
)


# Overall service score
interpret_ttest(
  
  "Service.Score",
  
  "Overall Service Score"
  
)


# ============================================================
# 11.4 COMPARISON OF VARIANCES
# Added from second method
# ============================================================


cat("
------------------------------------------------------------
11.4 COMPARISON OF VARIANCES
------------------------------------------------------------
")


# Levene / Brown-Forsythe

cat(
  "\nLevene test: Age across Satisfaction\n"
)

print(
  
  car::leveneTest(
    
    Age ~ Satisfaction,
    
    data =
      airline_clean
    
  )
  
)


cat(
  "\nLevene test: Overall Service Score across Class\n"
)

print(
  
  car::leveneTest(
    
    Service.Score ~ Class,
    
    data =
      airline_clean
    
  )
  
)


# ============================================================
# 11.5 ONE-WAY ANOVA
# ============================================================


cat("
------------------------------------------------------------
11.5 ONE-WAY ANOVA
------------------------------------------------------------
")


run_anova <- function(
    
  variable,
  
  group_variable =
    "Class"
  
) {
  
  
  formula <- as.formula(
    
    paste(
      
      variable,
      
      "~",
      
      group_variable
      
    )
    
  )
  
  
  model <- aov(
    
    formula,
    
    data =
      airline_clean
    
  )
  
  
  anova_table <-
    summary(
      model
    )[[1]]
  
  
  eta_squared <-
    
    anova_table[
      "Sum Sq"
    ][1, 1] /
    
    sum(
      anova_table[
        "Sum Sq"
      ][, 1]
    )
  
  
  welch <- oneway.test(
    
    formula,
    
    data =
      airline_clean,
    
    var.equal =
      FALSE
    
  )
  
  
  kruskal <- kruskal.test(
    
    formula,
    
    data =
      airline_clean
    
  )
  
  
  cat(
    
    "\n",
    variable,
    
    "across",
    
    group_variable,
    
    "\n"
    
  )
  
  
  cat(
    
    "ANOVA F =",
    
    round(
      
      anova_table[["F value"]][1],
      
      3
      
    ),
    
    "\n"
    
  )
  
  
  cat(
    
    "ANOVA p-value =",
    
    fmt_p(
      
      anova_table[["Pr(>F)"]][1]
      
    ),
    
    "\n"
    
  )
  
  
  cat(
    
    "Eta-squared =",
    
    round(
      eta_squared,
      3
    ),
    
    "\n"
    
  )
  
  
  cat(
    
    "Welch ANOVA p-value =",
    
    fmt_p(
      welch$p.value
    ),
    
    "\n"
    
  )
  
  
  cat(
    
    "Kruskal-Wallis p-value =",
    
    fmt_p(
      kruskal$p.value
    ),
    
    "\n"
    
  )
  
  
  cat(
    "\nGroup means:\n"
  )
  
  
  print(
    
    airline_clean %>%
      
      group_by(
        .data[[group_variable]]
      ) %>%
      
      summarise(
        
        N =
          n(),
        
        Mean =
          mean(
            .data[[variable]]
          ),
        
        SD =
          sd(
            .data[[variable]]
          ),
        
        .groups =
          "drop"
        
      )
    
  )
  
  
  cat(
    "\nTukey HSD:\n"
  )
  
  
  print(
    TukeyHSD(
      model
    )
  )
  
  
  return(
    model
  )
  
}


anova_service <-
  run_anova(
    
    "Service.Score",
    
    "Class"
    
  )


anova_age <-
  run_anova(
    
    "Age",
    
    "Class"
    
  )


anova_distance <-
  run_anova(
    
    "Flight.Distance",
    
    "Class"
    
  )


# Departure Delay across Class
anova_departure <-
  run_anova(
    
    "Departure.Delay",
    
    "Class"
    
  )


# ============================================================
# 11.6 TWO-WAY ANOVA + INTERACTION
# Added from second method
# ============================================================


cat("
------------------------------------------------------------
11.6 TWO-WAY ANOVA
------------------------------------------------------------
")


two_way_model <- aov(
  
  Service.Score ~
    
    Class *
    
    Type.of.Travel,
  
  data =
    airline_clean
  
)


cat(
  "\nType II two-way ANOVA:\n"
)


print(
  
  car::Anova(
    
    two_way_model,
    
    type =
      "II"
    
  )
  
)


# ------------------------------------------------------------
# Interaction plot
# ------------------------------------------------------------

interaction_data <- airline_clean %>%
  
  group_by(
    
    Class,
    
    Type.of.Travel
    
  ) %>%
  
  summarise(
    
    Mean_Service_Score =
      mean(
        Service.Score
      ),
    
    .groups =
      "drop"
    
  )


ggplot(
  
  interaction_data,
  
  aes(
    
    x =
      Class,
    
    y =
      Mean_Service_Score,
    
    colour =
      Type.of.Travel,
    
    group =
      Type.of.Travel
    
  )
  
) +
  
  geom_line() +
  
  geom_point(
    size =
      3
  ) +
  
  labs(
    
    title =
      "Interaction: Class × Type of Travel",
    
    x =
      "Class",
    
    y =
      "Mean Service Score"
    
  ) +
  
  theme_minimal()


# ============================================================
# 11.7 MULTIPLE TESTING
# Added from second method
# ============================================================


cat("
------------------------------------------------------------
11.7 MULTIPLE-TESTING CORRECTION
------------------------------------------------------------
")


# Collect p-values from the major tests

p_values <- c(
  
  Gender_ChiSquare =
    chisq_gender$p.value,
  
  CustomerType_ChiSquare =
    chisq_customer_type$p.value,
  
  TravelType_ChiSquare =
    chisq_travel_type$p.value,
  
  Class_ChiSquare =
    chisq_class$p.value,
  
  Age_tTest =
    t.test(
      Age ~ Satisfaction,
      data =
        airline_clean
    )$p.value,
  
  Distance_tTest =
    t.test(
      Flight.Distance ~ Satisfaction,
      data =
        airline_clean
    )$p.value,
  
  DepartureDelay_tTest =
    t.test(
      Departure.Delay ~ Satisfaction,
      data =
        airline_clean
    )$p.value,
  
  ArrivalDelay_tTest =
    t.test(
      Arrival.Delay ~ Satisfaction,
      data =
        airline_clean
    )$p.value
  
)


bonferroni_results <- data.frame(
  
  Test =
    names(
      p_values
    ),
  
  Original_p =
    as.numeric(
      p_values
    ),
  
  Bonferroni_Adjusted_p =
    p.adjust(
      
      p_values,
      
      method =
        "bonferroni"
      
    )
  
)


print(
  bonferroni_results
)


# ============================================================
# STEP 11 END
# ============================================================


# ============================================================
# STEP 12. LOGISTIC REGRESSION
# ============================================================


cat("
============================================================
STEP 12: LOGISTIC REGRESSION
============================================================
")


# ------------------------------------------------------------
# Target definition
#
# 0 = Neutral or Dissatisfied
# 1 = Satisfied
# ------------------------------------------------------------

airline_clean$Satisfaction <- factor(
  
  airline_clean$Satisfaction,
  
  levels = c(
    
    "Neutral or Dissatisfied",
    
    "Satisfied"
    
  )
  
)


airline_clean$y <- as.integer(
  
  airline_clean$Satisfaction ==
    "Satisfied"
  
)


# ------------------------------------------------------------
# BASE VARIABLES
#
# IMPORTANT:
# Departure.Delay is used instead of Arrival.Delay in the main
# model because Arrival.Delay is highly correlated with
# Departure.Delay and occurs after the flight.
#
# Log transformations are used because distance and delays are
# strongly right-skewed.
# ------------------------------------------------------------

base_vars <- c(
  
  "Gender",
  
  "Age",
  
  "Customer.Type",
  
  "Type.of.Travel",
  
  "Class",
  
  "log_Flight.Distance",
  
  "log_Departure.Delay"
  
)


# ============================================================
# 12.1 BASELINE LOGISTIC REGRESSION MODEL
# ============================================================


baseline_formula <- reformulate(
  
  base_vars,
  
  response =
    "y"
  
)


baseline_model <- glm(
  
  baseline_formula,
  
  data =
    airline_clean,
  
  family =
    binomial(
      link =
        "logit"
    )
  
)


cat(
  "\nBASELINE MODEL\n"
)


summary(
  baseline_model
)


# ------------------------------------------------------------
# Baseline coefficients
# ------------------------------------------------------------

cat(
  "\nBaseline coefficients:\n"
)

print(
  coef(
    baseline_model
  )
)


# ------------------------------------------------------------
# Baseline odds ratios
# ------------------------------------------------------------

baseline_odds_ratios <- exp(
  
  coef(
    baseline_model
  )
  
)


cat(
  "\nBaseline odds ratios:\n"
)

print(
  baseline_odds_ratios
)


# ------------------------------------------------------------
# Baseline OR confidence intervals
# ------------------------------------------------------------

baseline_or_ci <- exp(
  
  cbind(
    
    OR =
      coef(
        baseline_model
      ),
    
    confint.default(
      baseline_model
    )
    
  )
  
)


cat(
  "\nBaseline ORs with 95% CI:\n"
)

print(
  baseline_or_ci
)


# ------------------------------------------------------------
# Baseline AIC / BIC / McFadden R2
# ------------------------------------------------------------

mcfadden_r2 <- function(
    model) {
  
  1 -
    model$deviance /
    model$null.deviance
  
}


cat(
  "\nBaseline AIC:",
  AIC(
    baseline_model
  ),
  "\n"
)


cat(
  "Baseline BIC:",
  BIC(
    baseline_model
  ),
  "\n"
)


cat(
  "Baseline McFadden R2:",
  round(
    mcfadden_r2(
      baseline_model
    ),
    4
  ),
  "\n"
)


# ============================================================
# 12.2 SERVICE LOGISTIC REGRESSION MODEL
# ============================================================


# ------------------------------------------------------------
# IMPORTANT CHANGE FROM ORIGINAL:
#
# ORIGINAL:
#   Service model = service ratings only
#
# NEW:
#   Service model =
#   baseline passenger/flight variables
#   +
#   14 service ratings
#   +
#   N/A flags
#
# This makes the service model a true extension of the baseline.
# ------------------------------------------------------------


service_formula <- reformulate(
  
  c(
    
    base_vars,
    
    service_vars,
    
    flag_vars
    
  ),
  
  response =
    "y"
  
)


service_model <- glm(
  
  service_formula,
  
  data =
    airline_clean,
  
  family =
    binomial(
      link =
        "logit"
    )
  
)


cat(
  "\nSERVICE MODEL\n"
)


summary(
  service_model
)


# ------------------------------------------------------------
# Service model coefficients
# ------------------------------------------------------------

cat(
  "\nService model coefficients:\n"
)

print(
  coef(
    service_model
  )
)


# ------------------------------------------------------------
# Service model odds ratios
# ------------------------------------------------------------

service_odds_ratios <- exp(
  
  coef(
    service_model
  )
  
)


cat(
  "\nService model odds ratios:\n"
)

print(
  service_odds_ratios
)


# ------------------------------------------------------------
# 95% CI
# ------------------------------------------------------------

service_or_ci <- exp(
  
  cbind(
    
    OR =
      coef(
        service_model
      ),
    
    confint.default(
      service_model
    )
    
  )
  
)


cat(
  "\nService model odds ratios with 95% CI:\n"
)

print(
  service_or_ci
)


# ------------------------------------------------------------
# Service model AIC / BIC / McFadden R2
# ------------------------------------------------------------

cat(
  "\nService model AIC:",
  AIC(
    service_model
  ),
  "\n"
)


cat(
  "Service model BIC:",
  BIC(
    service_model
  ),
  "\n"
)


cat(
  "Service model McFadden R2:",
  round(
    mcfadden_r2(
      service_model
    ),
    4
  ),
  "\n"
)


# ============================================================
# 12.3 FULL LOGISTIC REGRESSION MODEL
# ============================================================


# Arrival.Delay is added only for model comparison.
# It is NOT the preferred main model because it is highly
# correlated with Departure.Delay.


full_formula <- reformulate(
  
  c(
    
    base_vars,
    
    service_vars,
    
    flag_vars,
    
    "log_Arrival.Delay"
    
  ),
  
  response =
    "y"
  
)


full_model <- glm(
  
  full_formula,
  
  data =
    airline_clean,
  
  family =
    binomial(
      link =
        "logit"
    )
  
)


cat(
  "\nFULL MODEL\n"
)

summary(
  full_model
)


# ============================================================
# 12.4 NESTED MODEL COMPARISON
# Added from second method
# ============================================================


cat("
------------------------------------------------------------
12.4 NESTED MODEL COMPARISON
------------------------------------------------------------
")


# ------------------------------------------------------------
# Baseline vs Service
#
# Question:
# Do service ratings add information beyond passenger and
# flight variables?
# ------------------------------------------------------------

cat(
  "\nBaseline vs Service Model:\n"
)

print(
  
  anova(
    
    baseline_model,
    
    service_model,
    
    test =
      "Chisq"
    
  )
  
)


# ------------------------------------------------------------
# Service vs Full
#
# Question:
# Does Arrival.Delay add information beyond the service model
# and Departure.Delay?
# ------------------------------------------------------------

cat(
  "\nService vs Full Model:\n"
)

print(
  
  anova(
    
    service_model,
    
    full_model,
    
    test =
      "Chisq"
    
  )
  
)


# ------------------------------------------------------------
# Model comparison table
# ------------------------------------------------------------

model_comparison <- data.frame(
  
  Model = c(
    
    "Baseline",
    
    "Service",
    
    "Full"
    
  ),
  
  Parameters = c(
    
    length(
      coef(
        baseline_model
      )
    ),
    
    length(
      coef(
        service_model
      )
    ),
    
    length(
      coef(
        full_model
      )
    )
    
  ),
  
  AIC = c(
    
    AIC(
      baseline_model
    ),
    
    AIC(
      service_model
    ),
    
    AIC(
      full_model
    )
    
  ),
  
  BIC = c(
    
    BIC(
      baseline_model
    ),
    
    BIC(
      service_model
    ),
    
    BIC(
      full_model
    )
    
  ),
  
  McFadden_R2 = c(
    
    mcfadden_r2(
      baseline_model
    ),
    
    mcfadden_r2(
      service_model
    ),
    
    mcfadden_r2(
      full_model
    )
    
  )
  
)


cat(
  "\nModel comparison:\n"
)

print(
  model_comparison
)


# ============================================================
# 12.5 STEPWISE MODEL SELECTION
# Added from second method
# ============================================================


cat("
------------------------------------------------------------
12.5 STEPWISE MODEL SELECTION
------------------------------------------------------------
")


RUN_STEPWISE <- TRUE


if (
  RUN_STEPWISE
) {
  
  
  # ----------------------------------------------------------
  # Backward AIC
  # ----------------------------------------------------------
  
  cat(
    "\nRunning backward AIC selection...\n"
  )
  
  
  stepwise_backward_AIC <-
    
    MASS::stepAIC(
      
      full_model,
      
      direction =
        "backward",
      
      trace =
        0
      
    )
  
  
  cat(
    "\nBackward AIC model:\n"
  )
  
  print(
    summary(
      stepwise_backward_AIC
    )
  )
  
  
  # ----------------------------------------------------------
  # Forward AIC
  # ----------------------------------------------------------
  
  cat(
    "\nRunning forward AIC selection...\n"
  )
  
  
  null_model <- glm(
    
    y ~ 1,
    
    data =
      airline_clean,
    
    family =
      binomial
    
  )
  
  
  stepwise_forward_AIC <-
    
    MASS::stepAIC(
      
      null_model,
      
      scope =
        list(
          
          lower =
            ~1,
          
          upper =
            full_formula
          
        ),
      
      direction =
        "forward",
      
      trace =
        0
      
    )
  
  
  cat(
    "\nForward AIC model:\n"
  )
  
  print(
    summary(
      stepwise_forward_AIC
    )
  )
  
  
  # ----------------------------------------------------------
  # Backward BIC
  # ----------------------------------------------------------
  
  cat(
    "\nRunning backward BIC selection...\n"
  )
  
  
  stepwise_backward_BIC <-
    
    MASS::stepAIC(
      
      full_model,
      
      direction =
        "backward",
      
      k =
        log(
          nrow(
            airline_clean
          )
        ),
      
      trace =
        0
      
    )
  
  
  cat(
    "\nBackward BIC model:\n"
  )
  
  print(
    summary(
      stepwise_backward_BIC
    )
  )
  
  
} else {
  
  
  stepwise_backward_AIC <-
    service_model
  
  stepwise_forward_AIC <-
    service_model
  
  stepwise_backward_BIC <-
    service_model
  
}


# ------------------------------------------------------------
# Number of coefficients retained
# ------------------------------------------------------------

cat(
  
  "\nNumber of predictor coefficients:\n",
  
  "Backward AIC =",
  
  length(
    coef(
      stepwise_backward_AIC
    )
  ) - 1,
  
  "\n",
  
  "Forward AIC =",
  
  length(
    coef(
      stepwise_forward_AIC
    )
  ) - 1,
  
  "\n",
  
  "Backward BIC =",
  
  length(
    coef(
      stepwise_backward_BIC
    )
  ) - 1,
  
  "\n"
  
)


# ------------------------------------------------------------
# Variables dropped
# ------------------------------------------------------------

cat(
  "\nVariables dropped by backward AIC:\n"
)

print(
  
  setdiff(
    
    names(
      coef(
        full_model
      )
    ),
    
    names(
      coef(
        stepwise_backward_AIC
      )
    )
    
  )
  
)


# ============================================================
# 12.6 BEST-SUBSET SCREENING
# Added from second method
# ============================================================


cat("
------------------------------------------------------------
12.6 BEST-SUBSET SCREENING
------------------------------------------------------------
")


# Important:
# With many predictors, checking all possible logistic models
# becomes computationally expensive.
#
# Therefore, as in the second script, we screen the 14 service
# ratings using a linear probability model.
#
# This is a model-selection SCREENING exercise, not the final
# logistic model.


best_subset <- leaps::regsubsets(
  
  reformulate(
    service_vars,
    "y"
  ),
  
  data =
    airline_clean,
  
  nvmax =
    length(
      service_vars
    )
  
)


best_subset_summary <-
  summary(
    best_subset
  )


best_k <-
  
  which.min(
    best_subset_summary$bic
  )


cat(
  "\nBest subset according to BIC keeps",
  best_k,
  "of",
  length(
    service_vars
  ),
  "service variables.\n"
)


cat(
  "\nSelected service variables:\n"
)


print(
  
  names(
    coef(
      best_subset,
      best_k
    )
  )[-1]
  
)


# ============================================================
# 12.7 RIDGE / LASSO / ELASTIC NET
# Added from second method
# ============================================================


cat("
------------------------------------------------------------
12.7 RIDGE / LASSO / ELASTIC NET
------------------------------------------------------------
")


# ------------------------------------------------------------
# Model matrix for the full predictor set
# ------------------------------------------------------------

X_train <- model.matrix(
  
  full_formula,
  
  data =
    airline_clean
  
)[, -1]


y_train <-
  airline_clean$y


# ------------------------------------------------------------
# Create common cross-validation folds
# ------------------------------------------------------------

set.seed(
  SEED
)


fold_id <- sample(
  
  rep(
    
    seq_len(
      N_FOLDS
    ),
    
    length.out =
      nrow(
        X_train
      )
    
  )
  
)


# ------------------------------------------------------------
# Ridge
# alpha = 0
# ------------------------------------------------------------

set.seed(
  SEED
)


cv_ridge <- cv.glmnet(
  
  X_train,
  
  y_train,
  
  family =
    "binomial",
  
  alpha =
    0,
  
  foldid =
    fold_id,
  
  type.measure =
    "deviance"
  
)


# ------------------------------------------------------------
# LASSO
# alpha = 1
# ------------------------------------------------------------

set.seed(
  SEED
)


cv_lasso <- cv.glmnet(
  
  X_train,
  
  y_train,
  
  family =
    "binomial",
  
  alpha =
    1,
  
  foldid =
    fold_id,
  
  type.measure =
    "deviance"
  
)


# ------------------------------------------------------------
# Elastic Net
# alpha = 0.5
# ------------------------------------------------------------

set.seed(
  SEED
)


cv_elastic_net <- cv.glmnet(
  
  X_train,
  
  y_train,
  
  family =
    "binomial",
  
  alpha =
    0.5,
  
  foldid =
    fold_id,
  
  type.measure =
    "deviance"
  
)


# ------------------------------------------------------------
# Lambda values
# ------------------------------------------------------------

cat(
  "\nRidge lambda.min:",
  cv_ridge$lambda.min,
  "\n"
)


cat(
  "Ridge lambda.1se:",
  cv_ridge$lambda.1se,
  "\n"
)


cat(
  "LASSO lambda.min:",
  cv_lasso$lambda.min,
  "\n"
)


cat(
  "LASSO lambda.1se:",
  cv_lasso$lambda.1se,
  "\n"
)


cat(
  "Elastic Net lambda.min:",
  cv_elastic_net$lambda.min,
  "\n"
)


cat(
  "Elastic Net lambda.1se:",
  cv_elastic_net$lambda.1se,
  "\n"
)


# ------------------------------------------------------------
# LASSO coefficients at lambda.1se
# ------------------------------------------------------------

lasso_coef <- as.matrix(
  
  coef(
    
    cv_lasso,
    
    s =
      "lambda.1se"
    
  )
  
)


cat(
  "\nLASSO coefficients at lambda.1se:\n"
)

print(
  lasso_coef
)


# ------------------------------------------------------------
# Variables retained by LASSO
# ------------------------------------------------------------

lasso_selected <- rownames(
  
  lasso_coef
  
)[
  
  lasso_coef[, 1] != 0
  
]


lasso_selected <- lasso_selected[
  
  lasso_selected !=
    "(Intercept)"
  
]


cat(
  "\nVariables retained by LASSO:\n"
)

print(
  lasso_selected
)


# ------------------------------------------------------------
# Delay coefficient comparison
#
# This helps illustrate how regularisation handles correlated
# delay variables.
# ------------------------------------------------------------

delay_terms <- c(
  
  "log_Departure.Delay",
  
  "log_Arrival.Delay"
  
)


coef_compare <- data.frame(
  
  Variable =
    delay_terms,
  
  Ordinary_Full_Logistic =
    
    sapply(
      
      delay_terms,
      
      function(term) {
        
        if (
          term %in%
          names(
            coef(
              full_model
            )
          )
        ) {
          
          coef(
            full_model
          )[term]
          
        } else {
          
          NA
          
        }
        
      }
      
    ),
  
  Ridge =
    
    sapply(
      
      delay_terms,
      
      function(term) {
        
        cm <-
          as.matrix(
            
            coef(
              
              cv_ridge,
              
              s =
                "lambda.1se"
              
            )
            
          )
        
        if (
          term %in%
          rownames(cm)
        ) {
          
          cm[
            term,
            1
          ]
          
        } else {
          
          NA
          
        }
        
      }
      
    ),
  
  LASSO =
    
    sapply(
      
      delay_terms,
      
      function(term) {
        
        if (
          term %in%
          rownames(
            lasso_coef
          )
        ) {
          
          lasso_coef[
            term,
            1
          ]
          
        } else {
          
          NA
          
        }
        
      }
      
    )
  
)


cat(
  "\nDelay coefficient comparison:\n"
)

print(
  coef_compare
)


# ============================================================
# 12.8 CROSS-VALIDATED LOGISTIC REGRESSION
# Added from second method
#
# IMPORTANT:
# This is cross-validation INSIDE the training dataset.
# The independent TEST set is kept untouched for Vidu's later
# model evaluation.
# ============================================================


cat("
------------------------------------------------------------
12.8 CROSS-VALIDATION
------------------------------------------------------------
")


cv_glm <- function(
    
  formula,
  
  data,
  
  k =
    N_FOLDS,
  
  seed =
    SEED
  
) {
  
  
  set.seed(
    seed
  )
  
  
  folds <- createFolds(
    
    data$Satisfaction,
    
    k =
      k
    
  )
  
  
  results <- lapply(
    
    folds,
    
    function(test_rows) {
      
      
      train_rows <- setdiff(
        
        seq_len(
          nrow(data)
        ),
        
        test_rows
        
      )
      
      
      fit <- glm(
        
        formula,
        
        data =
          data[
            train_rows,
          ],
        
        family =
          binomial
        
      )
      
      
      probabilities <- predict(
        
        fit,
        
        newdata =
          data[
            test_rows,
          ],
        
        type =
          "response"
        
      )
      
      
      actual <- data$y[
        test_rows
      ]
      
      
      accuracy <-
        
        mean(
          
          (
            probabilities >=
              0.50
          ) == actual
          
        )
      
      
      brier <-
        
        mean(
          
          (
            probabilities -
              actual
          )^2
          
        )
      
      
      roc_object <- pROC::roc(
        
        actual,
        
        probabilities,
        
        levels =
          c(
            0,
            1
          ),
        
        direction =
          "<",
        
        quiet =
          TRUE
        
      )
      
      
      auc <-
        
        as.numeric(
          
          pROC::auc(
            roc_object
          )
          
        )
      
      
      c(
        
        AUC =
          auc,
        
        Accuracy =
          accuracy,
        
        Brier =
          brier
        
      )
      
    }
    
  )
  
  
  do.call(
    rbind,
    results
  )
  
}


# ------------------------------------------------------------
# Cross-validation for baseline
# ------------------------------------------------------------

cv_baseline <- cv_glm(
  
  baseline_formula,
  
  airline_clean
  
)


# ------------------------------------------------------------
# Cross-validation for service model
# ------------------------------------------------------------

cv_service <- cv_glm(
  
  service_formula,
  
  airline_clean
  
)


# ------------------------------------------------------------
# Cross-validation for full model
# ------------------------------------------------------------

cv_full <- cv_glm(
  
  full_formula,
  
  airline_clean
  
)


# ------------------------------------------------------------
# CV summary
# ------------------------------------------------------------

cv_summary <- data.frame(
  
  Model = c(
    
    "Baseline",
    
    "Service",
    
    "Full"
    
  ),
  
  Mean_AUC = c(
    
    mean(
      cv_baseline[
        ,
        "AUC"
      ]
    ),
    
    mean(
      cv_service[
        ,
        "AUC"
      ]
    ),
    
    mean(
      cv_full[
        ,
        "AUC"
      ]
    )
    
  ),
  
  SD_AUC = c(
    
    sd(
      cv_baseline[
        ,
        "AUC"
      ]
    ),
    
    sd(
      cv_service[
        ,
        "AUC"
      ]
    ),
    
    sd(
      cv_full[
        ,
        "AUC"
      ]
    )
    
  ),
  
  Mean_Accuracy = c(
    
    mean(
      cv_baseline[
        ,
        "Accuracy"
      ]
    ),
    
    mean(
      cv_service[
        ,
        "Accuracy"
      ]
    ),
    
    mean(
      cv_full[
        ,
        "Accuracy"
      ]
    )
    
  ),
  
  Mean_Brier = c(
    
    mean(
      cv_baseline[
        ,
        "Brier"
      ]
    ),
    
    mean(
      cv_service[
        ,
        "Brier"
      ]
    ),
    
    mean(
      cv_full[
        ,
        "Brier"
      ]
    )
    
  )
  
)


cat(
  "\nCross-validation summary:\n"
)

print(
  cv_summary
)


# ============================================================
# 12.9 PREDICTED PROBABILITIES ON TRAINING DATA
#
# We do NOT evaluate on the independent test set here.
# Vidu's model-evaluation section will use the test set.
# ============================================================


cat("
------------------------------------------------------------
12.9 TRAINING-SET PREDICTED PROBABILITIES
------------------------------------------------------------
")


airline_clean$baseline_probability <- predict(
  
  baseline_model,
  
  newdata =
    airline_clean,
  
  type =
    "response"
  
)


airline_clean$service_probability <- predict(
  
  service_model,
  
  newdata =
    airline_clean,
  
  type =
    "response"
  
)


head(
  
  airline_clean[
    
    c(
      
      "Satisfaction",
      
      "baseline_probability",
      
      "service_probability"
      
    )
    
  ]
  
)


# ============================================================
# 12.10 SERVICE MODEL ODDS-RATIO TABLE
# ============================================================


service_or_table <- data.frame(
  
  Variable =
    names(
      coef(
        service_model
      )
    ),
  
  Coefficient =
    coef(
      service_model
    ),
  
  Odds_Ratio =
    exp(
      coef(
        service_model
      )
    ),
  
  P_Value =
    summary(
      service_model
    )$coefficients[
      ,
      4
    ]
  
)


service_or_table$Significant_0.05 <-
  
  service_or_table$P_Value < 0.05


cat(
  "\nService model OR table:\n"
)

print(
  service_or_table
)


# ============================================================
# SAVE IMPORTANT STEP 1-12 OUTPUTS
# ============================================================


write.csv(
  
  data_dictionary,
  
  "data_dictionary.csv",
  
  row.names =
    FALSE
  
)


write.csv(
  
  desc_table,
  
  "descriptive_statistics.csv",
  
  row.names =
    FALSE
  
)


write.csv(
  
  service_desc,
  
  "service_rating_statistics.csv",
  
  row.names =
    FALSE
  
)


write.csv(
  
  top_pairs,
  
  "top_service_correlation_pairs.csv",
  
  row.names =
    FALSE
  
)


write.csv(
  
  target_correlation,
  
  "correlation_with_satisfaction.csv",
  
  row.names =
    FALSE
  
)


write.csv(
  
  cramers_results,
  
  "cramers_v_results.csv",
  
  row.names =
    FALSE
  
)


write.csv(
  
  bonferroni_results,
  
  "multiple_testing_results.csv",
  
  row.names =
    FALSE
  
)


write.csv(
  
  model_comparison,
  
  "logistic_model_comparison.csv",
  
  row.names =
    FALSE
  
)


write.csv(
  
  cv_summary,
  
  "logistic_cross_validation.csv",
  
  row.names =
    FALSE
  
)


write.csv(
  
  service_or_table,
  
  "service_logistic_odds_ratios.csv",
  
  row.names =
    FALSE
  
)


# ============================================================
# ============================================================
# STEPS 13 - 22   (Vidu)
#
# These steps REUSE objects created in Steps 1-12:
#   airline_clean  -> TRAINING data (cleaned, imputed, logs, y)
#   test           -> TEST data (same preprocessing, never used
#                     for fitting or for choosing thresholds)
#   baseline_model, service_model, full_model
#   service_formula, baseline_formula, full_formula
#   service_vars, flag_vars, base_vars
#
# Run the whole file top to bottom (Steps 1-12 first).
# All new outputs are saved in the folder: outputs_13_22/
# ============================================================
# ============================================================

OUT <- "outputs_13_22"
dir.create(OUT, showWarnings = FALSE)

png_open <- function(name, w = 1000, h = 700) {
  png(file.path(OUT, name), width = w, height = h, res = 120)
}
save_csv <- function(x, name) {
  write.csv(x, file.path(OUT, name), row.names = FALSE)
}

# ------------------------------------------------------------
# Prepare TEST set exactly like the training set
# ------------------------------------------------------------
train_df <- airline_clean

test$Satisfaction <- factor(
  test$Satisfaction,
  levels = c("Neutral or Dissatisfied", "Satisfied")
)
test$y <- as.integer(test$Satisfaction == "Satisfied")

cat("\nTRAIN rows:", nrow(train_df), "| TEST rows:", nrow(test), "\n")

# Age bands (used in several later steps)
age_breaks <- c(0, 25, 35, 45, 55, Inf)
age_labels <- c("<=25", "26-35", "36-45", "46-55", "56+")
train_df$Age.Band <- cut(train_df$Age, age_breaks, labels = age_labels)
test$Age.Band     <- cut(test$Age,     age_breaks, labels = age_labels)

# Small helper: AUC of predicted probabilities
auc_of <- function(y, p) {
  as.numeric(pROC::auc(pROC::roc(y, p, levels = c(0, 1),
                                 direction = "<", quiet = TRUE)))
}


# ============================================================
# STEP 13. MODEL DIAGNOSTICS
#   13.1 VIF   13.2 Odds ratios   13.3 Assumptions
# Diagnostics are run on the SERVICE model (the main model).
# ============================================================

cat("
============================================================
STEP 13: MODEL DIAGNOSTICS
============================================================
")

# ------------------------------------------------------------
# 13.1 VIF (multicollinearity)
# GVIF^(1/(2*Df)) is comparable across numeric and factor terms.
# Rule of thumb: adjusted GVIF > 2.24 (= VIF 5) needs attention,
# > 3.16 (= VIF 10) is serious.
# ------------------------------------------------------------

vif_raw <- tryCatch(car::vif(service_model), error = function(e) NULL)

if (!is.null(vif_raw)) {
  if (is.matrix(vif_raw)) {
    vif_table <- data.frame(
      Variable      = rownames(vif_raw),
      GVIF          = vif_raw[, "GVIF"],
      Df            = vif_raw[, "Df"],
      Adjusted_GVIF = vif_raw[, "GVIF^(1/(2*Df))"]
    )
  } else {
    vif_table <- data.frame(
      Variable      = names(vif_raw),
      GVIF          = as.numeric(vif_raw),
      Df            = 1,
      Adjusted_GVIF = sqrt(as.numeric(vif_raw))
    )
  }
  vif_table$Flag <- ifelse(vif_table$Adjusted_GVIF > 3.16, "SERIOUS",
                    ifelse(vif_table$Adjusted_GVIF > 2.24, "CHECK", "OK"))
  vif_table <- vif_table[order(-vif_table$Adjusted_GVIF), ]
  rownames(vif_table) <- NULL
  cat("\n13.1 VIF table (service model):\n")
  print(vif_table)
  save_csv(vif_table, "step13_vif.csv")
} else {
  cat("\nVIF could not be computed (aliased coefficients?).\n")
  vif_table <- NULL
}

# ------------------------------------------------------------
# 13.2 Odds ratios with 95% Wald confidence intervals
# ------------------------------------------------------------

ci_wald <- confint.default(service_model)
coef_sum <- summary(service_model)$coefficients

or_table <- data.frame(
  Variable   = rownames(coef_sum),
  Coef       = coef_sum[, "Estimate"],
  Odds_Ratio = exp(coef_sum[, "Estimate"]),
  CI_Lower   = exp(ci_wald[rownames(coef_sum), 1]),
  CI_Upper   = exp(ci_wald[rownames(coef_sum), 2]),
  P_Value    = coef_sum[, "Pr(>|z|)"]
)
or_table$Direction <- ifelse(or_table$P_Value >= 0.05, "Not significant",
                      ifelse(or_table$Odds_Ratio > 1, "Increases odds of satisfaction",
                                                      "Decreases odds of satisfaction"))
rownames(or_table) <- NULL

cat("\n13.2 Odds ratios (service model):\n")
print(
  transform(or_table,
            Odds_Ratio = round(Odds_Ratio, 3),
            CI_Lower   = round(CI_Lower, 3),
            CI_Upper   = round(CI_Upper, 3),
            P_Value    = fmt_p(P_Value))[, -2]
)
save_csv(or_table, "step13_odds_ratios.csv")

# Forest plot of the service-rating odds ratios
fp <- or_table[or_table$Variable %in% service_vars, ]
fp <- fp[order(fp$Odds_Ratio), ]
png_open("step13_forest_plot.png")
par(mar = c(5, 15, 3, 2))
plot(fp$Odds_Ratio, seq_len(nrow(fp)), xlim = range(c(fp$CI_Lower, fp$CI_Upper)),
     pch = 19, yaxt = "n", ylab = "", xlab = "Odds ratio (per 1-point rating increase)",
     main = "Service ratings: odds ratios with 95% CI")
segments(fp$CI_Lower, seq_len(nrow(fp)), fp$CI_Upper, seq_len(nrow(fp)))
axis(2, at = seq_len(nrow(fp)), labels = gsub("\\.", " ", fp$Variable), las = 1, cex.axis = 0.8)
abline(v = 1, lty = 2, col = "red")
dev.off()

# ------------------------------------------------------------
# 13.3 Logistic regression ASSUMPTIONS
# ------------------------------------------------------------

cat("\n13.3 Assumption checks\n")

# A. Binary outcome, independent observations
cat("\nA. Outcome is binary (0/1):", all(train_df$y %in% c(0, 1)), "\n")
cat("   Duplicate rows remaining:", sum(duplicated(train_df)),
    "(duplicates were removed in Step 6; each row = one passenger)\n")

# B. Sample size / events per variable
n_events    <- min(table(train_df$y))
n_params    <- length(coef(service_model)) - 1
epv         <- n_events / n_params
cat("B. Events per variable (EPV):", round(epv, 1), "(>= 10 is the usual minimum)\n")

# C. Multicollinearity -> see VIF above
if (!is.null(vif_table)) {
  cat("C. Variables with adjusted GVIF > 2.24:",
      ifelse(any(vif_table$Adjusted_GVIF > 2.24),
             paste(vif_table$Variable[vif_table$Adjusted_GVIF > 2.24], collapse = ", "),
             "none"), "\n")
}

# D. Linearity of the logit for continuous predictors
#    (i) empirical-logit plots   (ii) Box-Tidwell style test
cont_vars <- c("Age", "log_Flight.Distance", "log_Departure.Delay")

png_open("step13_linearity_logit.png", w = 1400, h = 500)
par(mfrow = c(1, 3))
for (v in cont_vars) {
  brk <- unique(quantile(train_df[[v]], probs = seq(0, 1, 0.1)))
  bin <- cut(train_df[[v]], brk, include.lowest = TRUE)
  s   <- tapply(train_df$y, bin, sum)
  n   <- tapply(train_df$y, bin, length)
  xm  <- tapply(train_df[[v]], bin, mean)
  plot(xm, log((s + 0.5) / (n - s + 0.5)), type = "b", pch = 19,
       xlab = v, ylab = "Empirical logit", main = paste("Logit vs", v))
}
dev.off()

bt_test <- function(v) {
  d <- train_df
  shift <- ifelse(min(d[[v]]) <= 0, 1 - min(d[[v]]), 0)
  d$.bt <- (d[[v]] + shift) * log(d[[v]] + shift)
  m <- glm(update(service_formula, . ~ . + .bt), data = d, family = binomial)
  data.frame(Variable = v,
             BoxTidwell_Coef = unname(coef(m)[".bt"]),
             P_Value = summary(m)$coefficients[".bt", "Pr(>|z|)"])
}
bt_results <- do.call(rbind, lapply(cont_vars, bt_test))
bt_results$Conclusion <- ifelse(bt_results$P_Value < 0.05,
                                "Non-linearity detected (check plot; large n flags tiny deviations)",
                                "Linearity acceptable")
cat("\nD. Box-Tidwell linearity test:\n")
print(bt_results)
save_csv(bt_results, "step13_box_tidwell.csv")

# E. Influential observations
cd <- cooks.distance(service_model)
n_infl <- sum(cd > 4 / nrow(train_df), na.rm = TRUE)
cat("\nE. Cook's distance: max =", round(max(cd, na.rm = TRUE), 4),
    "| observations above 4/n:", n_infl,
    "(", round(100 * n_infl / length(cd), 2), "%)\n")
cat("   Observations with Cook's D > 1:", sum(cd > 1, na.rm = TRUE), "\n")

png_open("step13_cooks_distance.png")
plot(cd, type = "h", ylab = "Cook's distance", xlab = "Observation",
     main = "Influence diagnostics")
abline(h = 4 / nrow(train_df), col = "red", lty = 2)
dev.off()

std_res <- rstandard(service_model, type = "deviance")
cat("   |Standardised deviance residuals| > 3:", sum(abs(std_res) > 3, na.rm = TRUE), "\n")

# F. Separation / fitted probabilities at 0 or 1
fit_p <- fitted(service_model)
cat("F. Fitted probabilities < 1e-8 or > 1-1e-8:",
    sum(fit_p < 1e-8 | fit_p > 1 - 1e-8), "(0 = no sign of separation)\n")
cat("   Model converged:", service_model$converged, "\n")

# G. Goodness of fit: Hosmer-Lemeshow + McFadden pseudo R-squared
hl_test <- function(y, p, g = 10) {
  br  <- unique(quantile(p, probs = seq(0, 1, length.out = g + 1)))
  bin <- cut(p, br, include.lowest = TRUE)
  obs <- tapply(y, bin, sum)
  ev  <- tapply(p, bin, sum)
  n   <- tapply(y, bin, length)
  stat <- sum((obs - ev)^2 / (ev * (1 - ev / n)))
  df   <- length(n) - 2
  list(statistic = stat, df = df, p_value = pchisq(stat, df, lower.tail = FALSE))
}
hl <- hl_test(train_df$y, fit_p)
cat("\nG. Hosmer-Lemeshow: chi-sq =", round(hl$statistic, 2), ", df =", hl$df,
    ", p =", fmt_p(hl$p_value), "\n")
cat("   (With very large n this test rejects easily; rely on calibration plot in Step 14.)\n")

mcfadden <- 1 - service_model$deviance / service_model$null.deviance
cat("   McFadden pseudo R-squared:", round(mcfadden, 4), "\n")
cat("   Null deviance:", round(service_model$null.deviance, 1),
    "| Residual deviance:", round(service_model$deviance, 1),
    "| AIC:", round(AIC(service_model), 1), "\n")

assumption_summary <- data.frame(
  Assumption = c("Binary outcome", "Independent observations", "Enough events per variable",
                 "No serious multicollinearity", "Linearity of logit", "No extreme influential points",
                 "No separation", "Model fit"),
  Result = c("Met", "Met (duplicates removed; observational survey)",
             ifelse(epv >= 10, "Met", "NOT met"),
             ifelse(!is.null(vif_table) && any(vif_table$Adjusted_GVIF > 3.16), "Problem", "Met / acceptable"),
             ifelse(any(bt_results$P_Value < 0.05), "Check plots", "Met"),
             ifelse(sum(cd > 1, na.rm = TRUE) == 0, "Met (no Cook's D > 1)", "Check"),
             ifelse(sum(fit_p < 1e-8 | fit_p > 1 - 1e-8) == 0, "Met", "Check"),
             paste0("McFadden R2 = ", round(mcfadden, 3)))
)
cat("\nAssumption summary:\n")
print(assumption_summary)
save_csv(assumption_summary, "step13_assumption_summary.csv")


# ============================================================
# STEP 14. MODEL EVALUATION  (on the UNSEEN TEST SET)
#   Confusion matrix, sensitivity/specificity, ROC-AUC
# ============================================================

cat("
============================================================
STEP 14: MODEL EVALUATION (TEST SET)
============================================================
")

p_test <- list(
  Baseline = predict(baseline_model, newdata = test, type = "response"),
  Service  = predict(service_model,  newdata = test, type = "response"),
  Full     = predict(full_model,     newdata = test, type = "response")
)
p_train_service <- predict(service_model, newdata = train_df, type = "response")

# Threshold choice uses TRAINING data only (Youden's J) -> no test leakage
roc_train_service <- pROC::roc(train_df$y, p_train_service,
                               levels = c(0, 1), direction = "<", quiet = TRUE)
youden_threshold <- as.numeric(unlist(
  pROC::coords(roc_train_service, "best", ret = "threshold", best.method = "youden")
))[1]
cat("\nYouden-optimal threshold (from training data):", round(youden_threshold, 3), "\n")

class_metrics <- function(y, p, threshold = 0.5) {
  pred <- as.integer(p >= threshold)
  TP <- sum(pred == 1 & y == 1); TN <- sum(pred == 0 & y == 0)
  FP <- sum(pred == 1 & y == 0); FN <- sum(pred == 0 & y == 1)
  sens <- TP / (TP + FN); spec <- TN / (TN + FP)
  prec <- TP / (TP + FP)
  data.frame(
    Threshold = threshold, TP = TP, TN = TN, FP = FP, FN = FN,
    Accuracy = (TP + TN) / length(y),
    Sensitivity = sens, Specificity = spec,
    Precision_PPV = prec, NPV = TN / (TN + FN),
    F1 = 2 * prec * sens / (prec + sens),
    Balanced_Accuracy = (sens + spec) / 2
  )
}

# ------------------------------------------------------------
# 14.1 Confusion matrices
# ------------------------------------------------------------
eval_rows <- list()
for (m in names(p_test)) {
  cm <- table(Actual = factor(test$y, levels = c(0, 1), labels = c("Not satisfied", "Satisfied")),
              Predicted = factor(as.integer(p_test[[m]] >= 0.5), levels = c(0, 1),
                                 labels = c("Not satisfied", "Satisfied")))
  cat("\nConfusion matrix -", m, "model (threshold 0.50):\n")
  print(cm)
  eval_rows[[m]] <- cbind(Model = m, class_metrics(test$y, p_test[[m]], 0.5))
}
eval_rows[["Service (Youden)"]] <- cbind(
  Model = "Service (Youden)", class_metrics(test$y, p_test$Service, youden_threshold))

# ------------------------------------------------------------
# 14.2 ROC-AUC with 95% CI + DeLong comparison
# ------------------------------------------------------------
rocs <- lapply(p_test, function(p) pROC::roc(test$y, p, levels = c(0, 1),
                                             direction = "<", quiet = TRUE))
auc_tab <- data.frame(
  Model = names(rocs),
  AUC = sapply(rocs, function(r) as.numeric(pROC::auc(r))),
  CI_Lower = sapply(rocs, function(r) pROC::ci.auc(r)[1]),
  CI_Upper = sapply(rocs, function(r) pROC::ci.auc(r)[3])
)
rownames(auc_tab) <- NULL

eval_table <- do.call(rbind, eval_rows)
rownames(eval_table) <- NULL
eval_table <- merge(eval_table, auc_tab[, c("Model", "AUC")], by = "Model", all.x = TRUE)
eval_table$AUC[eval_table$Model == "Service (Youden)"] <- auc_tab$AUC[auc_tab$Model == "Service"]

cat("\n14.1 Classification metrics on TEST data:\n")
print(format(eval_table, digits = 3))
cat("\n14.2 AUC with 95% CI:\n")
print(auc_tab)

delong_bs <- pROC::roc.test(rocs$Baseline, rocs$Service, method = "delong")
delong_sf <- pROC::roc.test(rocs$Service,  rocs$Full,    method = "delong")
cat("\nDeLong test Baseline vs Service: p =", fmt_p(delong_bs$p.value), "\n")
cat("DeLong test Service vs Full:     p =", fmt_p(delong_sf$p.value), "\n")

# Overfitting check: train vs test AUC for the service model
auc_train_service <- as.numeric(pROC::auc(roc_train_service))
cat("\nService model AUC  train:", round(auc_train_service, 4),
    "| test:", round(auc_tab$AUC[auc_tab$Model == "Service"], 4), "\n")

save_csv(eval_table, "step14_classification_metrics.csv")
save_csv(auc_tab,    "step14_auc.csv")

# ROC plot
png_open("step14_roc_curves.png")
plot(rocs$Baseline, col = "grey40", legacy.axes = TRUE, lwd = 2,
     main = "ROC curves on TEST data")
plot(rocs$Service, col = "blue", add = TRUE, lwd = 2)
plot(rocs$Full,    col = "darkgreen", add = TRUE, lwd = 2, lty = 2)
legend("bottomright", bty = "n", lwd = 2, lty = c(1, 1, 2),
       col = c("grey40", "blue", "darkgreen"),
       legend = paste0(auc_tab$Model, " (AUC=", round(auc_tab$AUC, 3), ")"))
dev.off()

# Calibration plot (service model, deciles of predicted probability)
brk <- unique(quantile(p_test$Service, probs = seq(0, 1, 0.1)))
bin <- cut(p_test$Service, brk, include.lowest = TRUE)
cal <- data.frame(Predicted = tapply(p_test$Service, bin, mean),
                  Observed  = tapply(test$y, bin, mean))
png_open("step14_calibration.png")
plot(cal$Predicted, cal$Observed, pch = 19, xlim = c(0, 1), ylim = c(0, 1),
     xlab = "Mean predicted probability", ylab = "Observed proportion satisfied",
     main = "Calibration (TEST data)")
abline(0, 1, lty = 2, col = "red")
dev.off()
save_csv(cal, "step14_calibration_table.csv")

# Brier score
brier <- sapply(p_test, function(p) mean((p - test$y)^2))
cat("\nBrier scores (lower = better):\n")
print(round(brier, 4))


# ============================================================
# STEP 15. PCA EVALUATION
# Question: can the 14 correlated service ratings be summarised
# by a few components without losing predictive power?
# ============================================================

cat("
============================================================
STEP 15: PCA EVALUATION
============================================================
")

pca_input <- train_df[service_vars]
cor_service <- cor(pca_input)

# 15.1 Suitability for PCA
kmo <- psych::KMO(cor_service)
bart <- psych::cortest.bartlett(cor_service, n = nrow(pca_input))
cat("\n15.1 KMO overall MSA:", round(kmo$MSA, 3),
    "(>= 0.6 acceptable, >= 0.8 good)\n")
cat("     Bartlett's test of sphericity: chi-sq =", round(bart$chisq, 1),
    ", p =", fmt_p(bart$p.value), "\n")

# 15.2 PCA (standardised)
pca <- prcomp(pca_input, center = TRUE, scale. = TRUE)
eig <- pca$sdev^2
pca_var <- data.frame(
  Component = paste0("PC", seq_along(eig)),
  Eigenvalue = eig,
  Prop_Variance = eig / sum(eig),
  Cumulative = cumsum(eig / sum(eig))
)
cat("\n15.2 Variance explained:\n")
print(format(pca_var, digits = 3))

k_kaiser <- sum(eig > 1)
k_80     <- which(pca_var$Cumulative >= 0.80)[1]
cat("\nComponents with eigenvalue > 1 (Kaiser):", k_kaiser, "\n")
cat("Components needed for 80% variance:     ", k_80, "\n")

png_open("step15_scree_plot.png", w = 1200, h = 500)
par(mfrow = c(1, 2))
plot(eig, type = "b", pch = 19, xlab = "Component", ylab = "Eigenvalue", main = "Scree plot")
abline(h = 1, col = "red", lty = 2)
plot(pca_var$Cumulative, type = "b", pch = 19, ylim = c(0, 1),
     xlab = "Component", ylab = "Cumulative variance", main = "Cumulative variance")
abline(h = 0.8, col = "red", lty = 2)
dev.off()

# 15.3 Loadings (first components)
k_show <- max(k_kaiser, 3)
loadings_tab <- data.frame(Variable = service_vars,
                           round(pca$rotation[, seq_len(k_show), drop = FALSE], 3))
cat("\n15.3 Loadings:\n")
print(loadings_tab)
save_csv(pca_var, "step15_pca_variance.csv")
save_csv(loadings_tab, "step15_pca_loadings.csv")

# 15.4 Does PCA hurt prediction? Principal-components logistic regression
k_use <- k_80
pc_names <- paste0("PC", seq_len(k_use))

train_scores <- as.data.frame(pca$x[, seq_len(k_use), drop = FALSE])
test_scores  <- as.data.frame(predict(pca, newdata = test[service_vars])[, seq_len(k_use), drop = FALSE])

train_pc <- cbind(train_df, train_scores)
test_pc  <- cbind(test, test_scores)

pcr_formula <- reformulate(c(base_vars, pc_names), response = "y")
pcr_model   <- glm(pcr_formula, data = train_pc, family = binomial)
p_pcr       <- predict(pcr_model, newdata = test_pc, type = "response")

pca_compare <- data.frame(
  Model = c("Service (14 ratings + flags)", paste0("PCR (", k_use, " components)")),
  Num_Service_Predictors = c(length(service_vars) + length(flag_vars), k_use),
  Test_AUC = c(auc_of(test$y, p_test$Service), auc_of(test$y, p_pcr)),
  Test_Accuracy = c(mean((p_test$Service >= 0.5) == test$y), mean((p_pcr >= 0.5) == test$y)),
  AIC = c(AIC(service_model), AIC(pcr_model))
)
cat("\n15.4 PCA regression vs service model:\n")
print(format(pca_compare, digits = 4))
save_csv(pca_compare, "step15_pca_vs_service.csv")

auc_drop <- pca_compare$Test_AUC[1] - pca_compare$Test_AUC[2]
cat("\nPCA EVALUATION:\n")
cat(" - AUC loss from using", k_use, "components instead of the full set:", round(auc_drop, 4), "\n")
cat(ifelse(auc_drop < 0.01,
  " - PCA compresses the ratings with negligible loss -> useful for a SHORT survey / index.\n",
  " - PCA loses noticeable predictive power -> keep the individual ratings.\n"))
cat(" - BUT components are blends of ratings, so they cannot tell management WHICH service\n",
    "   to fix. Decision: keep the individual-rating logistic model for driver analysis;\n",
    "   use PCA only as a supporting summary / collinearity check.\n")


# ============================================================
# STEP 16. BAYESIAN METHODS EVALUATION
# No extra packages needed (conjugate Beta-Binomial + Laplace
# approximation). Optional full MCMC via rstanarm below.
# ============================================================

cat("
============================================================
STEP 16: BAYESIAN METHODS EVALUATION
============================================================
")

set.seed(SEED)

# 16.1 Beta-Binomial: posterior of satisfaction rate per segment
bayes_prop <- function(data, var, a0 = 1, b0 = 1) {
  lv <- levels(factor(data[[var]]))
  out <- lapply(lv, function(l) {
    y <- data$y[data[[var]] == l]
    s <- sum(y); n <- length(y)
    a <- a0 + s; b <- b0 + n - s
    data.frame(Variable = var, Level = l, n = n, Successes = s,
               Observed_Rate = s / n,
               Posterior_Mean = a / (a + b),
               CrI_Lower = qbeta(0.025, a, b),
               CrI_Upper = qbeta(0.975, a, b))
  })
  do.call(rbind, out)
}

bayes_segments <- rbind(
  bayes_prop(train_df, "Class"),
  bayes_prop(train_df, "Type.of.Travel"),
  bayes_prop(train_df, "Customer.Type"),
  bayes_prop(train_df, "Age.Band")
)
cat("\n16.1 Posterior satisfaction rates (uniform Beta(1,1) prior):\n")
print(format(bayes_segments, digits = 3))
save_csv(bayes_segments, "step16_bayes_segments.csv")

# 16.2 Posterior probability that one group beats another
prob_greater <- function(data, var, g1, g2, draws = 100000) {
  d1 <- data$y[data[[var]] == g1]; d2 <- data$y[data[[var]] == g2]
  t1 <- rbeta(draws, 1 + sum(d1), 1 + length(d1) - sum(d1))
  t2 <- rbeta(draws, 1 + sum(d2), 1 + length(d2) - sum(d2))
  c(P_g1_greater = mean(t1 > t2), Mean_Diff = mean(t1 - t2),
    Diff_Lower = unname(quantile(t1 - t2, 0.025)),
    Diff_Upper = unname(quantile(t1 - t2, 0.975)))
}
# Labels taken from the dataset itself (Class: Business/Economy/Economy Plus,
# Customer.Type: Returning/First-time, Type.of.Travel: Business/Personal)
cls    <- levels(factor(train_df$Class))
cust   <- levels(factor(train_df$Customer.Type))
travel <- levels(factor(train_df$Type.of.Travel))
pick <- function(lv, want) ifelse(want %in% lv, want, lv[1])

c_hi <- pick(cls, "Business");   c_lo <- pick(cls, "Economy")
u_hi <- pick(cust, "Returning"); u_lo <- pick(cust, "First-time")
t_hi <- pick(travel, "Business"); t_lo <- pick(travel, "Personal")

cmp <- data.frame(
  Comparison = c(paste("Class:", c_hi, "vs", c_lo),
                 paste("Customer:", u_hi, "vs", u_lo),
                 paste("Travel:", t_hi, "vs", t_lo)),
  rbind(
    prob_greater(train_df, "Class", c_hi, c_lo),
    prob_greater(train_df, "Customer.Type", u_hi, u_lo),
    prob_greater(train_df, "Type.of.Travel", t_hi, t_lo)
  )
)
cat("\n16.2 Posterior probability group 1 has higher satisfaction:\n")
print(format(cmp, digits = 3))
save_csv(cmp, "step16_bayes_group_comparisons.csv")

# 16.3 Prior sensitivity: does the prior matter?
overall_s <- sum(train_df$y); overall_n <- nrow(train_df)
sens_tab <- do.call(rbind, lapply(c(30, 300, overall_n), function(n) {
  idx <- sample(nrow(train_df), n)
  s <- sum(train_df$y[idx])
  data.frame(Sample_Size = n, Observed = s / n,
             Uniform_Prior_Mean  = (1 + s) / (2 + n),
             Skeptical_Beta_30_70 = (30 + s) / (100 + n))
}))
cat("\n16.3 Prior sensitivity (posterior mean satisfaction rate):\n")
print(format(sens_tab, digits = 4))
save_csv(sens_tab, "step16_prior_sensitivity.csv")

# 16.4 Bayesian logistic regression (Laplace approximation, flat prior):
# posterior ~ Normal(beta_hat, vcov). With ~100k rows the likelihood
# dominates any weak prior, so this matches the frequentist fit.
post_draws <- MASS::mvrnorm(n = 5000, mu = coef(service_model), Sigma = vcov(service_model))
post_or <- exp(post_draws)
bayes_or <- data.frame(
  Variable = colnames(post_or),
  Posterior_Median_OR = apply(post_or, 2, median),
  CrI_Lower = apply(post_or, 2, quantile, 0.025),
  CrI_Upper = apply(post_or, 2, quantile, 0.975),
  Prob_OR_gt_1 = apply(post_or, 2, function(x) mean(x > 1))
)
rownames(bayes_or) <- NULL
cat("\n16.4 Bayesian (Laplace) odds ratios for service ratings:\n")
print(format(bayes_or[bayes_or$Variable %in% service_vars, ], digits = 3))
save_csv(bayes_or, "step16_bayes_odds_ratios.csv")

# Optional: full MCMC (slow on 100k rows, so a subsample is used)
RUN_MCMC <- FALSE
if (RUN_MCMC && requireNamespace("rstanarm", quietly = TRUE)) {
  sub <- train_df[sample(nrow(train_df), 5000), ]
  bayes_fit <- rstanarm::stan_glm(service_formula, data = sub, family = binomial(),
                                  prior = rstanarm::normal(0, 2.5), seed = SEED, refresh = 0)
  print(summary(bayes_fit))
}

cat("\nBAYESIAN EVALUATION:\n")
cat(" - With ~100,000 passengers, posterior results ~ frequentist results (prior is swamped).\n")
cat(" - Bayesian value here: direct probability statements (e.g. P(Business > Eco)) that\n",
    "   managers understand, and stable estimates for SMALL segments / new routes.\n")
cat(" - Recommendation: keep frequentist logistic regression as the main method; use Bayesian\n",
    "   updating for small-sample or route-level monitoring.\n")


# ============================================================
# STEP 17. EXPERIMENTAL DESIGN EVALUATION  (CRD and RCBD)
#
# IMPORTANT: the airline data are OBSERVATIONAL - passengers were
# NOT randomly assigned to Class, service levels, etc. So CRD/RCBD
# cannot be applied to this dataset in the strict sense.
# We (a) show the observational ANALOGUES, (b) design the real
# experiment the airline SHOULD run to confirm causal effects.
# ============================================================

cat("
============================================================
STEP 17: EXPERIMENTAL DESIGN EVALUATION
============================================================
")

# 17.1 CRD analogue: one factor (Class), response = overall service score
crd <- aov(Service.Score ~ Class, data = train_df)
cat("\n17.1 CRD analogue: Service.Score ~ Class\n")
print(summary(crd))
print(TukeyHSD(crd))

set.seed(SEED)
shap_sample <- sample(residuals(crd), min(5000, length(residuals(crd))))
cat("\nCRD assumption checks:\n")
print(shapiro.test(shap_sample))
print(car::leveneTest(Service.Score ~ Class, data = train_df))

# 17.2 RCBD analogue: treatment = Class, block = Age band
# Cell means (one value per Class x Age band) give a classic RCBD layout.
cell_means <- aggregate(Service.Score ~ Class + Age.Band, data = train_df, FUN = mean)
cell_means$Age.Band <- factor(cell_means$Age.Band)
rcbd <- aov(Service.Score ~ Class + Age.Band, data = cell_means)
cat("\n17.2 RCBD analogue on cell means: Service.Score ~ Class + Age.Band(block)\n")
print(summary(rcbd))

# Relative efficiency of RCBD vs CRD
tab <- summary(rcbd)[[1]]
MS_block <- tab["Age.Band", "Mean Sq"]
MS_error <- tab["Residuals", "Mean Sq"]
b <- nlevels(cell_means$Age.Band); t_ <- nlevels(factor(cell_means$Class))
RE <- ((b - 1) * MS_block + b * (t_ - 1) * MS_error) / ((b * t_ - 1) * MS_error)
cat("\nRelative efficiency RCBD vs CRD:", round(RE, 2),
    ifelse(RE > 1, "(blocking by age band helps)", "(blocking adds little)"), "\n")

# 17.3 Proposed REAL experiment: RCBD with routes as blocks
set.seed(SEED)
treatments <- c("Control", "Improved Wi-Fi", "Improved Seat/Legroom Package")
blocks <- paste0("Route_", 1:6)
rcbd_layout <- do.call(rbind, lapply(blocks, function(bl) {
  data.frame(Block = bl, Treatment = sample(treatments))
}))
rcbd_layout$Flight_Slot <- rep(1:3, times = length(blocks))
cat("\n17.3 Proposed randomised RCBD layout (each route receives every treatment once):\n")
print(rcbd_layout)
save_csv(rcbd_layout, "step17_proposed_rcbd_layout.csv")

# 17.4 Sample size (power) for a one-way comparison of 3 treatments
within_var <- mean(tapply(train_df$Service.Score, train_df$Class, var))
effect <- c(0, 0.075, 0.15)           # smallest rating difference worth detecting
pw <- power.anova.test(groups = 3, between.var = var(effect),
                       within.var = within_var, power = 0.80, sig.level = 0.05)
cat("\n17.4 Passengers needed PER treatment group to detect a 0.15-point difference in",
    "\n     overall service score (80% power, alpha 0.05):", ceiling(pw$n), "\n")

cat("\nDESIGN EVALUATION:\n")
cat(" - CRD is suitable when units are homogeneous; RCBD when a known nuisance factor\n",
    "   (route, aircraft, season) exists -> for airlines, ROUTE/AIRCRAFT blocking is best.\n")
cat(" - Current data cannot prove causality. Recommended follow-up: pilot RCBD (layout above)\n",
    "   randomising service interventions within routes, then re-survey passengers.\n")

rd_summary <- data.frame(
  Item = c("CRD analogue p-value (Class)", "RCBD analogue p-value (Class)",
           "RCBD relative efficiency", "Passengers per group needed"),
  Value = c(signif(summary(crd)[[1]][["Pr(>F)"]][1], 3),
            signif(tab["Class", "Pr(>F)"], 3), round(RE, 2), ceiling(pw$n))
)
save_csv(rd_summary, "step17_design_summary.csv")


# ============================================================
# STEP 18. TIME-SERIES APPLICABILITY
# ============================================================

cat("
============================================================
STEP 18: TIME-SERIES APPLICABILITY
============================================================
")

# 18.1 Is there any date/time variable?
date_pattern <- "date|year|month|week|day|hour|timestamp|period|quarter"
cand <- grep(date_pattern, names(airline), ignore.case = TRUE, value = TRUE)
cat("\n18.1 Columns that look like dates:", ifelse(length(cand) == 0, "NONE", paste(cand, collapse = ", ")), "\n")
cat("     (Note: 'Departure.and.Arrival.Time.Convenience' is a RATING, not a timestamp.)\n")

# 18.2 Does row/ID order carry hidden time structure?
if ("ID" %in% names(train_df)) {
  ord <- train_df[order(train_df$ID), ]
  lb <- Box.test(ord$y, lag = 10, type = "Ljung-Box")
  cat("\n18.2 Ljung-Box test on satisfaction ordered by ID: p =", fmt_p(lb$p.value), "\n")
  png_open("step18_acf_by_id.png", w = 1000, h = 500)
  acf(ord$y, lag.max = 30, main = "ACF of satisfaction ordered by ID")
  dev.off()
  cat(ifelse(lb$p.value > 0.05,
             "     No autocorrelation: ID order is arbitrary, NOT a time index.\n",
             "     Some autocorrelation in ID order - confirm with the data owner what ID represents.\n"))
}

cat("\nTIME-SERIES EVALUATION:\n")
cat(" - The data is a single CROSS-SECTIONAL survey: one row per passenger, no date.\n")
cat(" - Time-series methods (ARIMA, seasonality, forecasting) are NOT applicable now.\n")
cat(" - They become applicable if the airline records monthly/route-level average satisfaction\n",
    "   (e.g. 24+ months) -> then use ARIMA / exponential smoothing, control charts, and\n",
    "   interrupted time-series to measure the effect of service improvements.\n")

ts_summary <- data.frame(
  Check = c("Date/time column present", "Autocorrelation by ID order", "Conclusion"),
  Result = c(ifelse(length(cand) == 0, "No", paste(cand, collapse = ", ")),
             ifelse(exists("lb"), paste0("Ljung-Box p = ", fmt_p(lb$p.value)), "ID missing"),
             "Not applicable to current cross-sectional data")
)
save_csv(ts_summary, "step18_timeseries_summary.csv")


# ============================================================
# STEP 19. BUSINESS INSIGHTS
# ============================================================

cat("
============================================================
STEP 19: BUSINESS INSIGHTS
============================================================
")

# 19.1 Importance of each service variable (Wald chi-square, type II)
imp <- tryCatch(as.data.frame(car::Anova(service_model, type = "II", test = "Wald")),
                error = function(e) NULL)

importance_tab <- data.frame(Variable = service_vars)
if (!is.null(imp)) {
  importance_tab$Wald_ChiSq <- imp[service_vars, "Chisq"]
} else {
  importance_tab$Wald_ChiSq <- (coef(service_model)[service_vars] /
    sqrt(diag(vcov(service_model))[service_vars]))^2
}
importance_tab$Odds_Ratio_per_point <- exp(coef(service_model)[service_vars])
importance_tab$Odds_Ratio_per_SD <- exp(coef(service_model)[service_vars] *
                                          sapply(train_df[service_vars], sd))
importance_tab$P_Value <- coef_sum[service_vars, "Pr(>|z|)"]

# 19.2 Performance: mean rating among passengers who actually used the service (0 = N/A)
raw_ratings <- train_raw[service_vars]
raw_ratings[raw_ratings == 0] <- NA
importance_tab$Mean_Rating <- colMeans(raw_ratings, na.rm = TRUE)
importance_tab$Pct_Low_Rating_1_2 <- colMeans(raw_ratings <= 2, na.rm = TRUE) * 100

sat_means <- sapply(split(raw_ratings, train_raw$Satisfaction), colMeans, na.rm = TRUE)
importance_tab$Gap_Satisfied_minus_Not <- sat_means[, "Satisfied"] - sat_means[, "Neutral or Dissatisfied"]

# 19.3 Importance-Performance quadrant
imp_cut  <- median(importance_tab$Wald_ChiSq)
perf_cut <- median(importance_tab$Mean_Rating)
importance_tab$Priority <- ifelse(
  importance_tab$Wald_ChiSq >= imp_cut & importance_tab$Mean_Rating <  perf_cut, "1. FIX FIRST (important, weak)",
  ifelse(importance_tab$Wald_ChiSq >= imp_cut & importance_tab$Mean_Rating >= perf_cut, "2. MAINTAIN (important, strong)",
  ifelse(importance_tab$Wald_ChiSq <  imp_cut & importance_tab$Mean_Rating <  perf_cut, "3. MONITOR (less important, weak)",
                                                                                     "4. LOW PRIORITY (less important, strong)")))
importance_tab <- importance_tab[order(-importance_tab$Wald_ChiSq), ]
rownames(importance_tab) <- NULL

cat("\n19.1-19.3 Service drivers, performance and priority:\n")
print(format(importance_tab, digits = 3))
save_csv(importance_tab, "step19_service_priority_table.csv")

# Importance-performance plot
png_open("step19_importance_performance.png", w = 1100, h = 800)
par(mar = c(5, 5, 3, 2))
plot(importance_tab$Mean_Rating, importance_tab$Wald_ChiSq, pch = 19, cex = 1.3,
     xlab = "Performance (mean rating, 1-5)", ylab = "Importance (Wald chi-square)",
     main = "Importance-Performance Matrix")
abline(v = perf_cut, h = imp_cut, lty = 2, col = "red")
text(importance_tab$Mean_Rating, importance_tab$Wald_ChiSq,
     gsub("\\.", " ", importance_tab$Variable), pos = 3, cex = 0.65)
text(min(importance_tab$Mean_Rating), max(importance_tab$Wald_ChiSq), "FIX FIRST",
     adj = c(0, 1), col = "red", font = 2)
dev.off()

# 19.4 Segment insights
seg_fun <- function(var) {
  d <- aggregate(y ~ get(var), data = train_df, FUN = function(z) c(Rate = mean(z), n = length(z)))
  data.frame(Segment = var, Level = d[[1]], Satisfaction_Rate = d$y[, "Rate"], n = d$y[, "n"])
}
segment_tab <- rbind(seg_fun("Class"), seg_fun("Type.of.Travel"),
                     seg_fun("Customer.Type"), seg_fun("Age.Band"), seg_fun("Gender"))
segment_tab <- segment_tab[order(segment_tab$Satisfaction_Rate), ]
rownames(segment_tab) <- NULL
cat("\n19.4 Satisfaction rate by segment (lowest first):\n")
print(format(segment_tab, digits = 3))
save_csv(segment_tab, "step19_segment_satisfaction.csv")

png_open("step19_segments.png", w = 1100, h = 700)
par(mar = c(5, 12, 3, 2))
barplot(rev(segment_tab$Satisfaction_Rate),
        names.arg = rev(paste(segment_tab$Segment, segment_tab$Level, sep = ": ")),
        horiz = TRUE, las = 1, cex.names = 0.8, xlim = c(0, 1),
        xlab = "Satisfaction rate", main = "Satisfaction by passenger segment")
abline(v = mean(train_df$y), lty = 2, col = "red")
dev.off()

# 19.5 Delay effect
delay_band <- cut(train_df$Departure.Delay, c(-Inf, 0, 15, 60, Inf),
                  labels = c("On time", "1-15 min", "16-60 min", ">60 min"))
delay_tab <- aggregate(train_df$y, list(Delay = delay_band), mean)
names(delay_tab)[2] <- "Satisfaction_Rate"
cat("\n19.5 Satisfaction by departure delay:\n")
print(delay_tab)
save_csv(delay_tab, "step19_delay_effect.csv")

fix_first <- importance_tab$Variable[grepl("^1", importance_tab$Priority)]
cat("\nKEY INSIGHTS (auto-generated):\n")
cat(" 1. Top 3 drivers by importance:", paste(head(importance_tab$Variable, 3), collapse = ", "), "\n")
cat(" 2. FIX FIRST areas:", ifelse(length(fix_first) == 0, "none", paste(fix_first, collapse = ", ")), "\n")
cat(" 3. Lowest-satisfaction segment:", segment_tab$Segment[1], "=", as.character(segment_tab$Level[1]),
    "(", round(100 * segment_tab$Satisfaction_Rate[1], 1), "% satisfied )\n")
cat(" NOTE: these are associations from observational survey data, not proven causes.\n")


# ============================================================
# STEP 20. PASSENGER SATISFACTION DECISION SUPPORT SYSTEM (DSS)
#   (a) Score any passenger   (b) Find best improvement levers
#   (c) Simulate fleet-wide improvements  (d) Segment risk report
# ============================================================

cat("
============================================================
STEP 20: PASSENGER SATISFACTION DECISION SUPPORT SYSTEM
============================================================
")

RISK_LOW  <- 0.35    # below this  -> HIGH RISK of dissatisfaction
RISK_HIGH <- 0.65    # above this  -> LIKELY SATISFIED

risk_band <- function(p) {
  cut(p, c(-Inf, RISK_LOW, RISK_HIGH, Inf),
      labels = c("HIGH RISK (likely dissatisfied)", "WATCH (uncertain)", "LIKELY SATISFIED"))
}

# (a) Score passengers ------------------------------------------------
score_passengers <- function(newdata, model = service_model) {
  if (!"log_Flight.Distance" %in% names(newdata))
    newdata$log_Flight.Distance <- log(newdata$Flight.Distance)
  if (!"log_Departure.Delay" %in% names(newdata))
    newdata$log_Departure.Delay <- log1p(newdata$Departure.Delay)
  p <- predict(model, newdata = newdata, type = "response")
  data.frame(Probability_Satisfied = p, Risk_Band = risk_band(p))
}

# (b) Personal improvement levers: +1 rating point on each service ----
improvement_levers <- function(row, model = service_model, top = 3) {
  p0 <- predict(model, newdata = row, type = "response")
  gain <- sapply(service_vars, function(v) {
    flag <- paste0(v, "_NA")
    if (flag %in% names(row) && row[[flag]] == 1) return(NA_real_)   # service not used
    if (row[[v]] >= 5) return(NA_real_)                               # already maximum
    r <- row
    r[[v]] <- min(5, r[[v]] + 1)
    predict(model, newdata = r, type = "response") - p0
  })
  gain <- sort(gain, decreasing = TRUE, na.last = NA)
  data.frame(Service = names(gain), Gain_in_Probability = as.numeric(gain))[seq_len(min(top, length(gain))), ]
}

# Demo on one TEST passenger with a borderline-low predicted probability
demo_scores <- score_passengers(test)
demo_idx <- which.min(abs(demo_scores$Probability_Satisfied - 0.30))
demo_row <- test[demo_idx, ]

cat("\n20.1 DEMO PASSENGER\n")
print(demo_row[, c("Gender", "Age", "Customer.Type", "Type.of.Travel", "Class")])
cat("Predicted probability of being satisfied:", round(demo_scores$Probability_Satisfied[demo_idx], 3), "\n")
cat("Risk band:", as.character(demo_scores$Risk_Band[demo_idx]), "\n")
cat("Actual outcome:", as.character(demo_row$Satisfaction), "\n")
cat("Top improvement levers (+1 rating point):\n")
print(improvement_levers(demo_row))

# (c) Fleet-wide what-if: raise one service by +1 point for everyone below 5
p_before <- predict(service_model, newdata = test, type = "response")
whatif <- do.call(rbind, lapply(service_vars, function(v) {
  d <- test
  flag <- paste0(v, "_NA")
  eligible <- d[[v]] < 5
  if (flag %in% names(d)) eligible <- eligible & d[[flag]] != 1
  d[[v]][eligible] <- d[[v]][eligible] + 1
  p_after <- predict(service_model, newdata = d, type = "response")
  data.frame(Service = v,
             Passengers_Affected_Pct = 100 * mean(eligible),
             Mean_Probability_Before = mean(p_before),
             Mean_Probability_After = mean(p_after),
             Satisfaction_Rate_Gain_pp = 100 * (mean(p_after) - mean(p_before)))
}))
whatif <- whatif[order(-whatif$Satisfaction_Rate_Gain_pp), ]
rownames(whatif) <- NULL
cat("\n20.2 Simulated fleet-wide gain from +1 rating point (TEST data):\n")
print(format(whatif, digits = 3))
save_csv(whatif, "step20_whatif_simulation.csv")

png_open("step20_whatif_gain.png", w = 1100, h = 700)
par(mar = c(5, 15, 3, 2))
barplot(rev(whatif$Satisfaction_Rate_Gain_pp), names.arg = rev(gsub("\\.", " ", whatif$Service)),
        horiz = TRUE, las = 1, cex.names = 0.8,
        xlab = "Predicted gain in satisfaction rate (percentage points)",
        main = "Which +1 service improvement pays off most?")
dev.off()

# (d) Segment risk report
test_scored <- cbind(test, score_passengers(test))
segment_risk <- do.call(rbind, lapply(c("Class", "Type.of.Travel", "Customer.Type"), function(v) {
  d <- aggregate(cbind(Probability_Satisfied, High_Risk = Risk_Band == "HIGH RISK (likely dissatisfied)") ~
                   get(v), data = test_scored, FUN = mean)
  data.frame(Segment = v, Level = d[[1]],
             Mean_Predicted_Satisfaction = d$Probability_Satisfied,
             Share_High_Risk = d$High_Risk,
             n = as.numeric(table(test_scored[[v]])[as.character(d[[1]])]))
}))
cat("\n20.3 Segment risk report (TEST data):\n")
print(format(segment_risk, digits = 3))
save_csv(segment_risk, "step20_segment_risk.csv")

# Scored passenger list for action teams
dss_output <- data.frame(Row = seq_len(nrow(test_scored)),
                         Class = test_scored$Class,
                         Type.of.Travel = test_scored$Type.of.Travel,
                         Actual = test_scored$Satisfaction,
                         Probability_Satisfied = round(test_scored$Probability_Satisfied, 3),
                         Risk_Band = test_scored$Risk_Band)
save_csv(dss_output, "step20_dss_scored_passengers.csv")

# Decision rules table (for the report)
dss_rules <- data.frame(
  Risk_Band = c("HIGH RISK", "WATCH", "LIKELY SATISFIED"),
  Probability_Range = c(paste0("< ", RISK_LOW), paste0(RISK_LOW, " - ", RISK_HIGH), paste0("> ", RISK_HIGH)),
  Suggested_Action = c("Service recovery: follow-up contact, apology/compensation, fix top lever",
                       "Targeted improvement on the passenger's top lever(s)",
                       "Maintain service; invite to loyalty programme / referral")
)
cat("\n20.4 DSS decision rules:\n")
print(dss_rules)
save_csv(dss_rules, "step20_dss_decision_rules.csv")

cat("\nHow to use the DSS on a NEW passenger:\n")
cat("  new_p <- data.frame(Gender='Female', Age=40, Customer.Type='Returning',\n")
cat("                      Type.of.Travel='Business', Class='Economy', Flight.Distance=1200,\n")
cat("                      Departure.Delay=20, <14 service ratings>, <flag_NA columns = 0>)\n")
cat("  score_passengers(new_p);  improvement_levers(new_p[1, ])\n")


# ============================================================
# STEP 21. INDUSTRY EXPERT VALIDATION
# Real validation needs REAL experts. This step prepares:
#   (a) automatic face-validity checks (do signs make sense?)
#   (b) a structured questionnaire to give to experts
#   (c) a function that scores their answers (I-CVI)
# ============================================================

cat("
============================================================
STEP 21: INDUSTRY EXPERT VALIDATION
============================================================
")

# (a) Face validity: expected direction vs observed direction
face_validity <- data.frame(
  Variable = service_vars,
  Expected_Direction = "Positive (better rating -> higher satisfaction)",
  Observed_Coefficient = coef(service_model)[service_vars],
  Observed_P_Value = coef_sum[service_vars, "Pr(>|z|)"]
)
face_validity$Matches_Expectation <- ifelse(face_validity$Observed_P_Value >= 0.05,
  "Not significant - ask experts why",
  ifelse(face_validity$Observed_Coefficient > 0, "Yes", "NO - counter-intuitive, discuss with experts"))
rownames(face_validity) <- NULL
cat("\n21.1 Face-validity check of model signs:\n")
print(format(face_validity, digits = 3))
save_csv(face_validity, "step21_face_validity.csv")

# (b) Expert questionnaire template
expert_questions <- data.frame(
  Item = 1:10,
  Topic = c("Model choice", "Top drivers", "Top drivers", "Counter-intuitive results", "Delay effect",
            "Segments", "What-if simulation", "DSS risk bands", "Actionability", "Missing factors"),
  Question = c(
    "Is a logistic regression on passenger ratings an appropriate way to identify satisfaction drivers?",
    paste0("Do you agree these are the most important service areas: ",
           paste(head(importance_tab$Variable, 3), collapse = ", "), "?"),
    paste0("Do you agree these areas need urgent attention: ",
           ifelse(length(fix_first) == 0, "(none flagged)", paste(fix_first, collapse = ", ")), "?"),
    "Are the model results that look counter-intuitive (see face-validity table) plausible in practice?",
    "Is the estimated effect of departure delay on satisfaction realistic?",
    "Are the segment differences (class, travel type, loyalty, age) consistent with your experience?",
    "Are the simulated gains from +1 rating point realistic and achievable?",
    "Are the DSS risk bands (35% / 65%) and suggested actions sensible for operations?",
    "Can the recommendations be implemented within normal budget and operational limits?",
    "Which important factors are missing from the survey (e.g. price, route, crew behaviour)?"),
  Score_1_to_5 = NA, Comments = ""
)
save_csv(expert_questions, "step21_expert_questionnaire_TEMPLATE.csv")
cat("\nExpert questionnaire template saved: ", file.path(OUT, "step21_expert_questionnaire_TEMPLATE.csv"), "\n")
cat("Suggested experts: airline customer-experience manager, cabin-crew/in-flight service lead,\n",
    "airport operations manager, revenue/marketing analyst, aviation-industry academic.\n")

# (c) Scoring function for completed expert sheets (one CSV per expert)
#     Score 4-5 = relevant/agree. I-CVI >= 0.78 is acceptable with 6+ experts.
summarise_expert_validation <- function(files) {
  all <- do.call(rbind, lapply(seq_along(files), function(i) {
    d <- read.csv(files[i]); d$Expert <- paste0("Expert_", i); d
  }))
  res <- aggregate(Score_1_to_5 ~ Item + Topic, data = all,
                   FUN = function(z) c(Mean = mean(z, na.rm = TRUE),
                                       CVI = mean(z >= 4, na.rm = TRUE)))
  out <- data.frame(Item = res$Item, Topic = res$Topic,
                    Mean_Score = res$Score_1_to_5[, "Mean"], I_CVI = res$Score_1_to_5[, "CVI"])
  out$Verdict <- ifelse(out$I_CVI >= 0.78, "Validated", "REVISE")
  cat("\nScale-level CVI (average):", round(mean(out$I_CVI), 2), "\n")
  out[order(out$Item), ]
}
cat("\nAfter experts fill the template, run:\n")
cat("  summarise_expert_validation(c('expert1.csv','expert2.csv','expert3.csv'))\n")
cat("\nNOTE: no expert opinions have been invented here. Report expert feedback only after collecting it.\n")


# ============================================================
# STEP 22. FINAL RECOMMENDATIONS
# Built automatically from the results above.
# ============================================================

cat("
============================================================
STEP 22: FINAL RECOMMENDATIONS
============================================================
")

auc_service <- auc_tab$AUC[auc_tab$Model == "Service"]
auc_base    <- auc_tab$AUC[auc_tab$Model == "Baseline"]
acc_service <- eval_table$Accuracy[eval_table$Model == "Service"]
top_whatif  <- head(whatif, 3)
worst_seg   <- head(segment_tab[segment_tab$n >= 500, ], 2)

final_lines <- c(
  "AIRLINE PASSENGER SATISFACTION - FINAL RECOMMENDATIONS",
  "======================================================",
  "",
  "1. MODEL PERFORMANCE",
  sprintf("   - The service model predicts satisfaction on unseen passengers with AUC = %.3f and accuracy = %.1f%%.",
          auc_service, 100 * acc_service),
  sprintf("   - Passenger/flight details alone give AUC = %.3f; adding service ratings raises it by %.3f.",
          auc_base, auc_service - auc_base),
  "",
  "2. SERVICE AREAS TO PRIORITISE",
  sprintf("   - Most influential ratings: %s.", paste(head(importance_tab$Variable, 3), collapse = ", ")),
  sprintf("   - Important AND weakly rated (fix first): %s.",
          ifelse(length(fix_first) == 0, "none flagged", paste(fix_first, collapse = ", "))),
  sprintf("   - Largest simulated gain from +1 rating point: %s (+%.1f pp), %s (+%.1f pp), %s (+%.1f pp).",
          top_whatif$Service[1], top_whatif$Satisfaction_Rate_Gain_pp[1],
          top_whatif$Service[2], top_whatif$Satisfaction_Rate_Gain_pp[2],
          top_whatif$Service[3], top_whatif$Satisfaction_Rate_Gain_pp[3]),
  "",
  "3. PASSENGER SEGMENTS TO TARGET",
  sprintf("   - Lowest satisfaction: %s = %s (%.1f%%) and %s = %s (%.1f%%).",
          worst_seg$Segment[1], worst_seg$Level[1], 100 * worst_seg$Satisfaction_Rate[1],
          worst_seg$Segment[2], worst_seg$Level[2], 100 * worst_seg$Satisfaction_Rate[2]),
  "",
  "4. OPERATIONS",
  "   - Use the DSS (Step 20) to flag HIGH RISK passengers for service recovery.",
  "   - Monitor departure delay: satisfaction falls as delay increases (Step 19.5).",
  "",
  "5. METHODS DECISIONS",
  "   - Keep logistic regression with individual ratings as the main method (interpretable).",
  "   - PCA: use only as a supporting summary (Step 15).",
  "   - Bayesian: use for small segments / route-level updating (Step 16).",
  "   - Experimental design: run a randomised RCBD pilot by route to confirm causal effects (Step 17).",
  "   - Time series: not applicable now; start collecting dated, route-level satisfaction (Step 18).",
  "",
  "6. LIMITATIONS",
  "   - Observational, single-survey data: associations, NOT proven causes.",
  "   - Satisfaction and service ratings come from the same respondent (possible halo effect).",
  "   - 0 ratings were treated as Not Applicable (confirm with dataset documentation).",
  "   - Expert validation (Step 21) still has to be carried out with real experts.",
  "",
  "7. NEXT STEPS",
  "   (1) Validate findings with airline experts.  (2) Pilot the top improvement(s) with an RCBD.",
  "   (3) Re-survey and compare using time-stamped data.  (4) Retrain the model yearly."
)

cat(paste(final_lines, collapse = "\n"), "\n")
writeLines(final_lines, file.path(OUT, "step22_final_recommendations.txt"))

final_table <- data.frame(
  Area = c("Model", "Top drivers", "Fix first", "Best what-if lever", "Weakest segment", "Next experiment"),
  Recommendation = c(
    sprintf("Service logistic model (test AUC %.3f)", auc_service),
    paste(head(importance_tab$Variable, 3), collapse = ", "),
    ifelse(length(fix_first) == 0, "none flagged", paste(fix_first, collapse = ", ")),
    top_whatif$Service[1],
    paste(worst_seg$Segment[1], "=", worst_seg$Level[1]),
    "RCBD pilot with routes as blocks")
)
save_csv(final_table, "step22_final_recommendations_table.csv")


# ============================================================
# END OF STEPS 1 - 22
# ============================================================

cat("
============================================================
END OF STEPS 1 - 22
============================================================
STEP 1  - Business Problem                 [Pulindu]
STEP 2  - Import Dataset                   [Pulindu]
STEP 3  - Understand Variables             [Pulindu]
STEP 4  - Data Quality                     [Pulindu]
STEP 5  - Missing Values + Split           [Pulindu]
STEP 6  - Duplicates                       [Pulindu]
STEP 7  - Outlier Analysis                 [Pulindu]
STEP 8  - Descriptive Statistics            [Pulindu]
STEP 9  - EDA & Visualizations              [Pulindu]
STEP 10 - Correlation Analysis              [Pulindu]

STEP 11 - Statistical Inference             [Ayendri/Nisalma]
STEP 12 - Logistic Regression               [Ayendri/Nisalma]

STEP 13 - Model Diagnostics                [Vidu]
STEP 14 - Model Evaluation (test set)      [Vidu]
STEP 15 - PCA Evaluation                   [Vidu]
STEP 16 - Bayesian Methods Evaluation      [Vidu]
STEP 17 - Experimental Design (CRD/RCBD)   [Vidu]
STEP 18 - Time-Series Applicability        [Vidu]
STEP 19 - Business Insights                [Vidu]
STEP 20 - Decision Support System          [Vidu]
STEP 21 - Expert Validation                [Vidu]
STEP 22 - Final Recommendations            [Vidu]

All Step 13-22 outputs are in the folder: outputs_13_22/
============================================================
")
